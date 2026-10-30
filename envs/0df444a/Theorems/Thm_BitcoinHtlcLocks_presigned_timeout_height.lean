-- Prove2me | Theorems.Thm_BitcoinHtlcLocks_presigned_timeout_height
-- name    : BitcoinHtlcLocks.presigned_timeout_height
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T19:35:55.066431+00:00
-- url     : https://prove2.me/theorems/aed72bce-8d57-4ccf-bb03-bcb9aac7a76b
-- title:
--   A pre-signed HTLC-timeout transaction confirms only above the expiry height
-- statement:
--   For $0 < {\rm expiry} < 500{,}000{,}000$, a transaction with `nLockTime = expiry` and an in-range input whose `nSequence` is not final: `isFinalTx tx height blockTime = true` implies `expiry < height`. BOLT #3's HTLC-timeout transaction, which spends an offered HTLC with the 2-of-2 signatures, is built exactly so.
-- source:
--   BOLT #3, HTLC-Timeout and HTLC-Success Transactions (locktime = cltv_expiry), Received HTLC Outputs: https://github.com/lightning/bolts/blob/master/03-transactions.md#htlc-timeout-and-htlc-success-transactions; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: IsFinalTx (src/consensus/tx_verify.cpp) as the block mission's `isFinalTx`, ContextualCheckBlock (src/validation.cpp), GenericTransactionSignatureChecker::CheckLockTime (src/script/interpreter.cpp); BIP65

import Definitions.Def_BitcoinHtlcLocks
import Definitions.Def_BitcoinSer
open BitcoinHtlcLocks BitcoinVerify BitcoinHtlc
open BitcoinScript hiding Bytes Byte

theorem BitcoinHtlcLocks.presigned_timeout_height (tx : BitcoinSer.Tx) (expiry height : Nat) (blockTime : Int)
    (hexp : 0 < expiry ∧ expiry < BitcoinBlockV2.LOCKTIME_THRESHOLD) (htx : tx.nLockTime = expiry)
    (i : Nat) (hi : i < tx.vin.length)
    (hseq : (tx.vin.getD i ⟨⟨[], 0⟩, [], 0, []⟩).nSequence ≠ BitcoinBlockV2.SEQUENCE_FINAL)
    (hfinal : BitcoinBlockV2.isFinalTx tx height blockTime = true) : expiry < height := by sorry
