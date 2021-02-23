// SPDX-License-Identifier: MIT

pragma solidity >=0.6.0 <0.8.0;

/**
 * @dev Wrappers over Solidity's arithmetic operations with added overflow
 * checks.
 *
 * Arithmetic operations in Solidity wrap on overflow. This can easily result
 * in bugs, because programmers usually assume that an overflow raises an
 * error, which is the standard behavior in high level programming languages.
 * `SafeMath` restores this intuition by reverting the transaction when an
 * operation overflows.
 *
 * Using this library instead of the unchecked operations eliminates an entire
 * class of bugs, so it's recommended to use it always.
 */
library SafeMath {

    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");
        return c;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        require(b <= a, "SafeMath: subtraction overflow");
        return a - b;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        if (a == 0) return 0;
        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");
        return c;
    }

    /**
     * @dev Returns the integer division of two unsigned integers, reverting on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        require(b > 0, "SafeMath: division by zero");
        return a / b;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * reverting when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        require(b > 0, "SafeMath: modulo by zero");
        return a % b;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {trySub}.
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b <= a, errorMessage);
        return a - b;
    }
}

/*
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with GSN meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address payable) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes memory) {
        this; // silence state mutability warning without generating bytecode - see https://github.com/ethereum/solidity/issues/2691
        return msg.data;
    }
}

/**
 * @dev Interface of the BEP20 standard as defined in the EIP.
 */
interface IBEP20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address sender, address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);
}

/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
abstract contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor () internal {
        address msgSender = _msgSender();
        _owner = msgSender;
        emit OwnershipTransferred(address(0), msgSender);
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(owner() == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _owner = address(0);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }
}

/**
 * @dev Implementation of the {IBEP20} interface.
 *
 * This implementation is agnostic to the way tokens are created. This means
 * that a supply mechanism has to be added in a derived contract using {_mint}.
 * For a generic mechanism see {BEP20PresetMinterPauser}.
 *
 * TIP: For a detailed writeup see our guide
 * https://forum.zeppelin.solutions/t/how-to-implement-bep20-supply-mechanisms/226[How
 * to implement supply mechanisms].
 *
 * We have followed general OpenZeppelin guidelines: functions revert instead
 * of returning `false` on failure. This behavior is nonetheless conventional
 * and does not conflict with the expectations of BEP20 applications.
 *
 * Additionally, an {Approval} event is emitted on calls to {transferFrom}.
 * This allows applications to reconstruct the allowance for all accounts just
 * by listening to said events. Other implementations of the EIP may not emit
 * these events, as it isn't required by the specification.
 *
 * Finally, the non-standard {decreaseAllowance} and {increaseAllowance}
 * functions have been added to mitigate the well-known issues around setting
 * allowances. See {IBEP20-approve}.
 */
contract BEP20 is Context, IBEP20 {
    using SafeMath for uint256;

    mapping (address => uint256) private _balances;

    mapping (address => mapping (address => uint256)) private _allowances;

    uint256 private _totalSupply;

    string private _name;
    string private _symbol;
    uint8 private _decimals;

    /**
     * @dev Sets the values for {name} and {symbol}, initializes {decimals} with
     * a default value of 18.
     *
     * To select a different value for {decimals}, use {_setupDecimals}.
     *
     * All three of these values are immutable: they can only be set once during
     * construction.
     */
    constructor (string memory name_, string memory symbol_) public {
        _name = name_;
        _symbol = symbol_;
        _decimals = 18;
    }

    /**
     * @dev Returns the name of the token.
     */
    function name() public view virtual returns (string memory) {
        return _name;
    }

    /**
     * @dev Returns the symbol of the token, usually a shorter version of the
     * name.
     */
    function symbol() public view virtual returns (string memory) {
        return _symbol;
    }

    /**
     * @dev Returns the number of decimals used to get its user representation.
     * For example, if `decimals` equals `2`, a balance of `505` tokens should
     * be displayed to a user as `5,05` (`505 / 10 ** 2`).
     *
     * Tokens usually opt for a value of 18, imitating the relationship between
     * Ether and Wei. This is the value {BEP20} uses, unless {_setupDecimals} is
     * called.
     *
     * NOTE: This information is only used for _display_ purposes: it in
     * no way affects any of the arithmetic of the contract, including
     * {IBEP20-balanceOf} and {IBEP20-transfer}.
     */
    function decimals() public view virtual returns (uint8) {
        return _decimals;
    }

    /**
     * @dev See {IBEP20-totalSupply}.
     */
    function totalSupply() public view virtual override returns (uint256) {
        return _totalSupply;
    }

    /**
     * @dev See {IBEP20-balanceOf}.
     */
    function balanceOf(address account) public view virtual override returns (uint256) {
        return _balances[account];
    }

    /**
     * @dev See {IBEP20-transfer}.
     *
     * Requirements:
     *
     * - `recipient` cannot be the zero address.
     * - the caller must have a balance of at least `amount`.
     */
    function transfer(address recipient, uint256 amount) public virtual override returns (bool) {
        _transfer(_msgSender(), recipient, amount);
        return true;
    }

    /**
     * @dev See {IBEP20-allowance}.
     */
    function allowance(address owner, address spender) public view virtual override returns (uint256) {
        return _allowances[owner][spender];
    }

    /**
     * @dev See {IBEP20-approve}.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     */
    function approve(address spender, uint256 amount) public virtual override returns (bool) {
        _approve(_msgSender(), spender, amount);
        return true;
    }

    /**
     * @dev See {IBEP20-transferFrom}.
     *
     * Emits an {Approval} event indicating the updated allowance. This is not
     * required by the EIP. See the note at the beginning of {BEP20}.
     *
     * Requirements:
     *
     * - `sender` and `recipient` cannot be the zero address.
     * - `sender` must have a balance of at least `amount`.
     * - the caller must have allowance for ``sender``'s tokens of at least
     * `amount`.
     */
    function transferFrom(address sender, address recipient, uint256 amount) public virtual override returns (bool) {
        _transfer(sender, recipient, amount);
        _approve(sender, _msgSender(), _allowances[sender][_msgSender()].sub(amount, "BEP20: transfer amount exceeds allowance"));
        return true;
    }

    /**
     * @dev Atomically increases the allowance granted to `spender` by the caller.
     *
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IBEP20-approve}.
     *
     * Emits an {Approval} event indicating the updated allowance.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     */
    function increaseAllowance(address spender, uint256 addedValue) public virtual returns (bool) {
        _approve(_msgSender(), spender, _allowances[_msgSender()][spender].add(addedValue));
        return true;
    }

    /**
     * @dev Atomically decreases the allowance granted to `spender` by the caller.
     *
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IBEP20-approve}.
     *
     * Emits an {Approval} event indicating the updated allowance.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     * - `spender` must have allowance for the caller of at least
     * `subtractedValue`.
     */
    function decreaseAllowance(address spender, uint256 subtractedValue) public virtual returns (bool) {
        _approve(_msgSender(), spender, _allowances[_msgSender()][spender].sub(subtractedValue, "BEP20: decreased allowance below zero"));
        return true;
    }

    /**
     * @dev Moves tokens `amount` from `sender` to `recipient`.
     *
     * This is internal function is equivalent to {transfer}, and can be used to
     * e.g. implement automatic token fees, slashing mechanisms, etc.
     *
     * Emits a {Transfer} event.
     *
     * Requirements:
     *
     * - `sender` cannot be the zero address.
     * - `recipient` cannot be the zero address.
     * - `sender` must have a balance of at least `amount`.
     */
    function _transfer(address sender, address recipient, uint256 amount) internal virtual {
        require(sender != address(0), "BEP20: transfer from the zero address");
        require(recipient != address(0), "BEP20: transfer to the zero address");

        _beforeTokenTransfer(sender, recipient, amount);

        _balances[sender] = _balances[sender].sub(amount, "BEP20: transfer amount exceeds balance");
        _balances[recipient] = _balances[recipient].add(amount);
        emit Transfer(sender, recipient, amount);
    }

    /** @dev Creates `amount` tokens and assigns them to `account`, increasing
     * the total supply.
     *
     * Emits a {Transfer} event with `from` set to the zero address.
     *
     * Requirements:
     *
     * - `to` cannot be the zero address.
     */
    function _mint(address account, uint256 amount) internal virtual {
        require(account != address(0), "BEP20: mint to the zero address");

        _beforeTokenTransfer(address(0), account, amount);

        _totalSupply = _totalSupply.add(amount);
        _balances[account] = _balances[account].add(amount);
        emit Transfer(address(0), account, amount);
    }

    /**
     * @dev Destroys `amount` tokens from `account`, reducing the
     * total supply.
     *
     * Emits a {Transfer} event with `to` set to the zero address.
     *
     * Requirements:
     *
     * - `account` cannot be the zero address.
     * - `account` must have at least `amount` tokens.
     */
    function _burn(address account, uint256 amount) internal virtual {
        require(account != address(0), "BEP20: burn from the zero address");

        _beforeTokenTransfer(account, address(0), amount);

        _balances[account] = _balances[account].sub(amount, "BEP20: burn amount exceeds balance");
        _totalSupply = _totalSupply.sub(amount);
        emit Transfer(account, address(0), amount);
    }

    /**
     * @dev Sets `amount` as the allowance of `spender` over the `owner` s tokens.
     *
     * This internal function is equivalent to `approve`, and can be used to
     * e.g. set automatic allowances for certain subsystems, etc.
     *
     * Emits an {Approval} event.
     *
     * Requirements:
     *
     * - `owner` cannot be the zero address.
     * - `spender` cannot be the zero address.
     */
    function _approve(address owner, address spender, uint256 amount) internal virtual {
        require(owner != address(0), "BEP20: approve from the zero address");
        require(spender != address(0), "BEP20: approve to the zero address");

        _allowances[owner][spender] = amount;
        emit Approval(owner, spender, amount);
    }

    /**
     * @dev Sets {decimals} to a value other than the default one of 18.
     *
     * WARNING: This function should only be called from the constructor. Most
     * applications that interact with token contracts will not expect
     * {decimals} to ever change, and may work incorrectly if it does.
     */
    function _setupDecimals(uint8 decimals_) internal virtual {
        _decimals = decimals_;
    }

    /**
     * @dev Hook that is called before any transfer of tokens. This includes
     * minting and burning.
     *
     * Calling conditions:
     *
     * - when `from` and `to` are both non-zero, `amount` of ``from``'s tokens
     * will be to transferred to `to`.
     * - when `from` is zero, `amount` tokens will be minted for `to`.
     * - when `to` is zero, `amount` of ``from``'s tokens will be burned.
     * - `from` and `to` are never both zero.
     *
     * To learn more about hooks, head to xref:ROOT:extending-contracts.adoc#using-hooks[Using Hooks].
     */
    function _beforeTokenTransfer(address from, address to, uint256 amount) internal virtual { }
}


/**
 * @dev Extension of {BEP20} that allows token holders to destroy both their own
 * tokens and those that they have an allowance for, in a way that can be
 * recognized off-chain (via event analysis).
 */
abstract contract BEP20Burnable is Context, BEP20 {
    using SafeMath for uint256;

    /**
     * @dev Destroys `amount` tokens from the caller.
     *
     * See {BEP20-_burn}.
     */
    function burn(uint256 amount) public virtual {
        _burn(_msgSender(), amount);
    }

    /**
     * @dev Destroys `amount` tokens from `account`, deducting from the caller's
     * allowance.
     *
     * See {BEP20-_burn} and {BEP20-allowance}.
     *
     * Requirements:
     *
     * - the caller must have allowance for ``accounts``'s tokens of at least
     * `amount`.
     */
    function burnFrom(address account, uint256 amount) public virtual {
        uint256 decreasedAllowance = allowance(account, _msgSender()).sub(amount, "BEP20: burn amount exceeds allowance");

        _approve(account, _msgSender(), decreasedAllowance);
        _burn(account, amount);
    }
}

/**
 * @dev Extension of {BEP20} that adds a cap to the supply of tokens.
 */
abstract contract BEP20Capped is BEP20, Ownable {
    using SafeMath for uint256;

    uint256 private _cap;

    /**
     * @dev Sets the value of the `cap`. This value is immutable, it can only be
     * set once during construction.
     */
    constructor (uint256 cap_) internal {
        require(cap_ > 0, "BEP20Capped: cap is 0");
        _cap = cap_;
    }

    /**
     * @dev Returns the cap on the token's total supply.
     */
    function cap() public view virtual returns (uint256) {
        return _cap;
    }
    
    function addCap(uint256 amount) public virtual onlyOwner {
        _cap = _cap.add(amount);
    }


    /**
     * @dev See {BEP20-_beforeTokenTransfer}.
     *
     * Requirements:
     *
     * - minted tokens must not cause the total supply to go over the cap.
     */
    function _beforeTokenTransfer(address from, address to, uint256 amount) internal virtual override {
        super._beforeTokenTransfer(from, to, amount);

        if (from == address(0)) { // When minting tokens
            require(totalSupply().add(amount) <= cap(), "BEP20Capped: cap exceeded");
        }
    }
}

abstract contract StakeToken is Ownable, BEP20Capped, BEP20Burnable {
    using SafeMath for uint256;
    struct RewardInfoSnapshot {
        uint256 cap;
        uint256 rewardingStake;
        uint256 totalRewardingStakes;
        uint256 rewardingRatio;
        uint256 totalRewardingRatio;
    }
    // 18
    uint256 constant _ratioDecimal = 1000000000000000000;
    
    address constant WBTC_ADDRESS = 0x7130d2A12B9BCbFAe4f2634d864A1Ee1Ce3Ead9c;
    
    address[] internal _delegates;
    address[] internal _stakeholders;
    mapping(address => uint256) internal _rewardingStakes;
    mapping(address => uint256) internal _unenforcedStakes;
    mapping(address => uint256) internal _rewards;
    mapping(address => uint256) internal _rewardsHistory;
    mapping(address => uint256) internal _lastReward;
    mapping(address => RewardInfoSnapshot) internal _rewardingInfos;
    
    event CreateStakeEvt(address indexed account, uint256 stake);
    event RemoveStakeEvt(address indexed account, uint256 stake);
    event ReallocateStakesEvt();
    event DistributeRewardsEvt(address indexed account, uint256 cap, uint256 totalRewardingStakes, uint256 rewardingStake, uint256 reward);
    event DistributeTotalRewardsEvt(uint256 totalRewards);
    event CalculateRewardsRatioEvt(address indexed account, uint256 cap, uint256 totalRewardingStakes, uint256 rewardingStake, uint256 rewardRatio);
    event UnenforcedStakesTakeEffectEvt(address indexed account, uint256 stake);
    
    WBTC internal constant _wbtcToken = WBTC(WBTC_ADDRESS);
    
    constructor() {

    }
    
    function isStakeholder(address _address) public view virtual returns(bool, uint256) {
        for (uint256 s = 0; s < _stakeholders.length; s += 1) {
            if (_address == _stakeholders[s]) return (true, s);
        }
        return (false, 0);
    }

    function addStakeholder(address _stakeholder) internal virtual {
        (bool _isStakeholder, ) = isStakeholder(_stakeholder);
        if (!_isStakeholder) _stakeholders.push(_stakeholder);
    }

    function removeStakeholder(address _stakeholder) internal virtual {
        (bool _isStakeholder, uint256 s) = isStakeholder(_stakeholder);
        if (_isStakeholder) {
            _stakeholders[s] = _stakeholders[_stakeholders.length - 1];
            _stakeholders.pop();
            delete _rewardingStakes[_stakeholder];
            delete _unenforcedStakes[_stakeholder];
        }
    }
    
    function stakesOf(address _stakeholder) public view virtual returns(uint256) {
        return _rewardingStakes[_stakeholder].add(_unenforcedStakes[_stakeholder]);
    }

    function rewardingStakesOf(address _stakeholder) public view virtual returns(uint256) {
        return _rewardingStakes[_stakeholder];
    }
    
    function totalRewardingStakes() public view virtual returns(uint256) {
        uint256 _totalRewardingStakes = 0;
        for (uint256 s = 0; s < _stakeholders.length; s += 1){
            _totalRewardingStakes = _totalRewardingStakes.add(_rewardingStakes[_stakeholders[s]]);
        }
        return _totalRewardingStakes;
    }
    
    function totalUnenforcedStakes() public view virtual returns(uint256) {
        uint256 _totallUnenforcedStakes = 0;
        for (uint256 s = 0; s < _stakeholders.length; s += 1){
            _totallUnenforcedStakes = _totallUnenforcedStakes.add(_unenforcedStakes[_stakeholders[s]]);
        }
        return _totallUnenforcedStakes;
    }
    
    function totalStakes() public view virtual returns(uint256) {
        uint256 _totallStakes = 0;
        for (uint256 s = 0; s < _stakeholders.length; s += 1){
            _totallStakes = _totallStakes.add(_unenforcedStakes[_stakeholders[s]]);
            _totallStakes = _totallStakes.add(_rewardingStakes[_stakeholders[s]]);
        }
        return _totallStakes;
    }


    function createStake(uint256 _stake) public virtual {
        address _msgSender = _msgSender();
        require(balanceOf(_msgSender) >= _stake, "StakeToken: balance isn't enough to stake");
        _burn(_msgSender, _stake);
        if (_rewardingStakes[_msgSender] == 0 && _unenforcedStakes[_msgSender] == 0) addStakeholder(_msgSender);
        _unenforcedStakes[_msgSender] = _unenforcedStakes[_msgSender].add(_stake);
        emit CreateStakeEvt(_msgSender, _stake);
    }
    
    function removeStake(uint256 _stake) public virtual {
        address _msgSender = _msgSender();
        require(stakesOf(_msgSender) >= _stake, "StakeToken: stakes aren't enough to unstake");
        if (_rewardingStakes[_msgSender] >= _stake) {
            _rewardingStakes[_msgSender] = _rewardingStakes[_msgSender].sub(_stake);
        } else {
            uint256 _subtrack = _rewardingStakes[_msgSender];
            _rewardingStakes[_msgSender] = 0;
            uint256 _rest = _stake.sub(_subtrack);
            _unenforcedStakes[_msgSender] = _unenforcedStakes[_msgSender].sub(_rest);
        }
        if (_unenforcedStakes[_msgSender] == 0 && _rewardingStakes[_msgSender] == 0) removeStakeholder(_msgSender);
        _mint(_msgSender, _stake);
        emit RemoveStakeEvt(_msgSender, _stake);
    }

    function calculateRewards(address _stakeholder, uint256 _reward) public virtual canDelegate returns (uint256) {
        uint256 _60Percent = _ratioDecimal.mul(60).div(100);
        RewardInfoSnapshot memory _rewardInfoSnapshot = _rewardingInfos[_stakeholder];
        
        uint256 reward;
        delete _rewardingInfos[_stakeholder];
        if (_rewardInfoSnapshot.totalRewardingRatio < _60Percent) {
            reward = _rewardInfoSnapshot.rewardingRatio.mul(_reward.mul(_60Percent).div(_ratioDecimal)).div(_ratioDecimal);
        } else {
            reward = _rewardInfoSnapshot.rewardingRatio.mul(_reward).div(_ratioDecimal);
        }
        _rewards[_stakeholder] = _rewards[_stakeholder].add(reward);
        _rewardsHistory[_stakeholder] = _rewardsHistory[_stakeholder].add(reward);
        _lastReward[_stakeholder] = reward;
        emit DistributeRewardsEvt(_stakeholder, _rewardInfoSnapshot.cap, _rewardInfoSnapshot.totalRewardingStakes, _rewardInfoSnapshot.rewardingStake, reward);
        return reward;
    }

    function distributeRewards(uint256 _reward) public virtual canDelegate {
        require(_stakeholders.length > 0, "StakeToken: stake holders can't be zero");
        uint256 _totalRewards;
        for (uint256 s; s < _stakeholders.length; s += 1) {
            _totalRewards = _totalRewards.add(calculateRewards(_stakeholders[s], _reward));
        }
        emit DistributeTotalRewardsEvt(_totalRewards);
    }

    function lastRewardOf(address _stakeholder) public view virtual returns (uint256) {
        return _lastReward[_stakeholder];
    }
    
    function totalLastReward() public view virtual returns (uint256) {
        uint256 _totalLastReward;
        for (uint256 s = 0; s < _stakeholders.length; s += 1) {
            _totalLastReward = _totalLastReward.add(_lastReward[_stakeholders[s]]);
        }
        return _totalLastReward;
    }

    function balanceRewardsOf(address _stakeholder) public view virtual returns (uint256) {
        return _rewards[_stakeholder];
    }

    function totalBalanceRewards() public view virtual returns (uint256) {
        uint256 _totalBalanceRewards;
        for (uint256 s = 0; s < _stakeholders.length; s += 1) {
            _totalBalanceRewards = _totalBalanceRewards.add(_rewards[_stakeholders[s]]);
        }
        return _totalBalanceRewards;
    }

    function withdrawRewards(uint256 _amount) public virtual returns (bool) {
        require(_amount > 0, "StakeToken: withdraw amount can't be zero");
        address _msgSender = _msgSender();
        _rewards[_msgSender] = _rewards[_msgSender].sub(_amount, "StakeToken: left rewards aren't enough");
        if (!_wbtcToken.transfer(_msgSender, _amount)) {
            _rewards[_msgSender] = _rewards[_msgSender].add(_amount);
            return false;
        }
        return true;
    }
    
    function rewardsHistoryOf(address _stakeholder) public view virtual returns (uint256) {
        return _rewardsHistory[_stakeholder];
    }
    
    function totalRewardsHistory() public view virtual returns (uint256) {
        uint256 _totalRewardsHistory;
        for (uint256 s = 0; s < _stakeholders.length; s += 1) {
            _totalRewardsHistory = _totalRewardsHistory.add(_rewardsHistory[_stakeholders[s]]);
        }
        return _totalRewardsHistory;
    }
    
    function reallocateStakes() public virtual canDelegate {
        require(_stakeholders.length > 0, "StakeToken: stake holders can't be zero");
        uint256 _60Percent = _ratioDecimal.mul(60).div(100);
        uint256 _unenforcedStake;
        uint256 _rewardingRatio;
        uint256 _totalRewardingStakes = totalRewardingStakes();
        uint256 _cap = cap();
        uint256 _totalRewardingRatio = _totalRewardingStakes.mul(_ratioDecimal).div(_cap);
        RewardInfoSnapshot memory _rewardInfoSnapshot;
        for (uint256 s = 0; s < _stakeholders.length; s += 1) {
            _rewardInfoSnapshot.cap = _cap;
            address _stakeholder = _stakeholders[s];
            uint256 _rewardingStake = _rewardingStakes[_stakeholder];
            if (_totalRewardingStakes> 0) {
                if (_totalRewardingRatio < _60Percent) {
                    _rewardingRatio = _rewardingStake.mul(_ratioDecimal).div(_totalRewardingStakes);
                    
                } else {
                    _rewardingRatio = _rewardingStake.mul(_ratioDecimal).div(_cap);
                }
                _rewardInfoSnapshot = RewardInfoSnapshot(_cap, _rewardingStake, _totalRewardingStakes, _rewardingRatio, _totalRewardingRatio);
            }
            _rewardingInfos[_stakeholder] = _rewardInfoSnapshot;
            emit CalculateRewardsRatioEvt(_stakeholder, _cap, _totalRewardingStakes, _rewardingStake, _rewardingRatio);
            _unenforcedStake = _unenforcedStakes[_stakeholder];
            if (_unenforcedStake > 0) {
                _unenforcedStakes[_stakeholder] = 0;
                _rewardingStakes[_stakeholder] = _rewardingStakes[_stakeholder].add(_unenforcedStake);
                emit UnenforcedStakesTakeEffectEvt(_stakeholder, _unenforcedStake);
            }
            
        }
        emit ReallocateStakesEvt();
    }
    
    function delegate(address[] memory to) public virtual onlyOwner {
        require(to.length > 0, "StakeToken: delegate can't be zero");
        require(to.length <= 3, "StakeToken: delegate can't be larger then 3");
        _delegates = to;
    }
    
    function cancelDelegate() public virtual onlyOwner {
        delete _delegates;
    }
    
    function isDelegate(address _address) public view virtual returns(bool) {
        for (uint256 s = 0; s < _delegates.length; s += 1) {
            if (_address == _delegates[s]) return true;
        }
        return false;
    }
    
    function showDelegate() public view virtual returns(address[] memory) {
        return _delegates;
    }
    
    modifier canDelegate() {
        address _msgSender = _msgSender();
        require(isDelegate(_msgSender) || owner() == _msgSender, "StakeToken: caller is not the delegate or owner");
        _;
    }

    function _beforeTokenTransfer(address from, address to, uint256 amount) internal virtual override(BEP20, BEP20Capped) {
        if (from == address(0)) { // When minting tokens
            require(totalSupply().add(totalStakes()).add(amount) <= cap(), "BEP20Capped: cap exceeded");
        }
    }
}


contract BTCHT is BEP20("BTC Hashrate Token", "BTCHT"), Ownable, BEP20Capped(500000000000000000000000), BEP20Burnable, StakeToken {
    using SafeMath for uint256;
    
    function _beforeTokenTransfer(address from, address to, uint256 amount) internal override(BEP20, BEP20Capped, StakeToken) {
        super._beforeTokenTransfer(from, to, amount);
    }
    
    function mint(address _to, uint256 _amount) public onlyOwner returns (bool) {
        _mint(_to, _amount);
        return true;
    }
    
}

abstract contract WBTC {
    function transfer(address receiver, uint amount) public virtual returns (bool);
}
