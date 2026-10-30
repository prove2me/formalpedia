-- Prove2me | Theorems.Thm_BitcoinHtlcLocks_received_spend_height
-- name    : BitcoinHtlcLocks.received_spend_height
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T19:36:08.689982+00:00
-- url     : https://prove2.me/theorems/c07acd9f-63bd-4a0c-848e-575e7dc7bee7
-- title:
--   A received HTLC cannot be timed out before its expiry at the consensus level
-- statement:
--   For a context $c$ with the `WITNESS` and `CHECKLOCKTIMEVERIFY` flags, keys and hashes of at most 520 bytes, $0 < {\rm expiry} < 500{,}000{,}000$, and $c$'s input index in range: if `verifyScript` accepts the two-element witness `[sig, pk]` for the pay-to-witness-script-hash output of `receivedBytes revHash remoteKey localKey payHash expiry`, and $c$'s transaction is final at `height` (`isFinalTx c.tx height blockTime = true`, which `ContextualCheckBlock` requires of every transaction in a block at that height), then either `RevocationSpend c (receivedBytes …) revHash pk sig`, or `expiry < height`. The HTLC mission's script conditions and the block mission's finality rule compose: besides the revocation key, the only two-element witness is the timeout path, whose `OP_CHECKLOCKTIMEVERIFY` forces `nLockTime ≥ expiry` and a non-final input, and finality then forces `nLockTime < height`.
-- source:
--   BOLT #3, HTLC-Timeout and HTLC-Success Transactions (locktime = cltv_expiry), Received HTLC Outputs: https://github.com/lightning/bolts/blob/master/03-transactions.md#htlc-timeout-and-htlc-success-transactions; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: IsFinalTx (src/consensus/tx_verify.cpp) as the block mission's `isFinalTx`, ContextualCheckBlock (src/validation.cpp), GenericTransactionSignatureChecker::CheckLockTime (src/script/interpreter.cpp); BIP65

import Definitions.Def_BitcoinHtlcLocks
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinHtlc
open BitcoinHtlcLocks BitcoinVerify BitcoinHtlc
open BitcoinScript hiding Bytes Byte

theorem BitcoinHtlcLocks.received_spend_height (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (hcltv : c.flags.cltv = true)
    (revHash remoteKey localKey payHash : BitcoinSer.Bytes) (expiry : Int) (sig pk : BitcoinSer.Bytes)
    (hrev : revHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hrem : remoteKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hloc : localKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hexp : 0 < expiry ∧ expiry < BitcoinBlockV2.LOCKTIME_THRESHOLD) (hnIn : c.nIn < c.tx.vin.length)
    (hv : BitcoinVerify.verifyScript tap c []
        (BitcoinVerify.witnessBytes 0 (BitcoinSer.sha256 (BitcoinHtlc.receivedBytes revHash remoteKey localKey payHash expiry)))
        ([sig, pk] ++ [BitcoinHtlc.receivedBytes revHash remoteKey localKey payHash expiry]) = true)
    (height : Nat) (blockTime : Int) (hfinal : BitcoinBlockV2.isFinalTx c.tx height blockTime = true) :
    BitcoinHtlcLocks.RevocationSpend c (BitcoinHtlc.receivedBytes revHash remoteKey localKey payHash expiry) revHash pk sig ∨
      expiry < height := by sorry
