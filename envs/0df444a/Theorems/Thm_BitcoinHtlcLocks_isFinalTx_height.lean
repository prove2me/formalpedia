-- Prove2me | Theorems.Thm_BitcoinHtlcLocks_isFinalTx_height
-- name    : BitcoinHtlcLocks.isFinalTx_height
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T19:35:38.898273+00:00
-- url     : https://prove2.me/theorems/fd499025-4de4-4f40-87f8-c9bbb0ac05c1
-- title:
--   IsFinalTx for a height-locked transaction with a non-final input
-- statement:
--   For a transaction with `HeightLocked tx` and some input $i$ (in range) whose `nSequence` is not `0xffffffff`: `isFinalTx tx height blockTime = true ↔ tx.nLockTime < height`. The lock time is enforced as a block height, and the non-final input blocks the `SEQUENCE_FINAL` bypass.
-- source:
--   BOLT #3, HTLC-Timeout and HTLC-Success Transactions (locktime = cltv_expiry), Received HTLC Outputs: https://github.com/lightning/bolts/blob/master/03-transactions.md#htlc-timeout-and-htlc-success-transactions; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: IsFinalTx (src/consensus/tx_verify.cpp) as the block mission's `isFinalTx`, ContextualCheckBlock (src/validation.cpp), GenericTransactionSignatureChecker::CheckLockTime (src/script/interpreter.cpp); BIP65

import Definitions.Def_BitcoinHtlcLocks
import Definitions.Def_BitcoinSer
open BitcoinHtlcLocks BitcoinVerify BitcoinHtlc
open BitcoinScript hiding Bytes Byte

theorem BitcoinHtlcLocks.isFinalTx_height (tx : BitcoinSer.Tx) (height : Nat) (blockTime : Int)
    (hl : BitcoinHtlcLocks.HeightLocked tx) (i : Nat) (hi : i < tx.vin.length)
    (hseq : (tx.vin.getD i ⟨⟨[], 0⟩, [], 0, []⟩).nSequence ≠ BitcoinBlockV2.SEQUENCE_FINAL) :
    BitcoinBlockV2.isFinalTx tx height blockTime = true ↔ tx.nLockTime < height := by sorry
