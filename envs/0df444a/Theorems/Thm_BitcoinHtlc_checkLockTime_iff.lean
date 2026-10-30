-- Prove2me | Theorems.Thm_BitcoinHtlc_checkLockTime_iff
-- name    : BitcoinHtlc.checkLockTime_iff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T17:29:23.588768+00:00
-- url     : https://prove2.me/theorems/6a367ac5-c27a-47b8-a3ec-94bd57acb824
-- title:
--   CheckLockTime for a block-height expiry
-- statement:
--   For $0 \le {\rm expiry} < 500{,}000{,}000$: `checkLockTime tx nIn expiry = true` iff the transaction's `nLockTime` is also a block height (below 500,000,000), `expiry ≤ nLockTime`, and the input's `nSequence` is not `0xffffffff`. BIP65 as `GenericTransactionSignatureChecker::CheckLockTime` implements it.
-- source:
--   BOLT #3, Bitcoin Transaction and Script Formats, 'Offered HTLC Outputs' and 'Received HTLC Outputs': https://github.com/lightning/bolts/blob/master/03-transactions.md#offered-htlc-outputs; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_DUP, OP_HASH160, OP_EQUAL, OP_IF/OP_NOTIF, OP_SWAP, OP_SIZE, OP_CHECKMULTISIG, OP_CHECKLOCKTIMEVERIFY, OP_CHECKSIG), GenericTransactionSignatureChecker::CheckLockTime (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP65, BIP141, BIP147

import Definitions.Def_BitcoinHtlc
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinSig
import Definitions.Def_BitcoinToLocal
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinHtlc.checkLockTime_iff (tx : BitcoinSer.Tx) (nIn : Nat) (expiry : Int) (h0 : 0 ≤ expiry)
    (hT : expiry < 500000000) :
    BitcoinSig.checkLockTime tx nIn expiry = true ↔
      tx.nLockTime < 500000000 ∧ expiry ≤ (tx.nLockTime : Int) ∧ BitcoinToLocal.inputSequence tx nIn ≠ 0xffffffff := by sorry
