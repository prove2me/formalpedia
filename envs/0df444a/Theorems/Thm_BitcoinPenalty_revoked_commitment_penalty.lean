-- Prove2me | Theorems.Thm_BitcoinPenalty_revoked_commitment_penalty
-- name    : BitcoinPenalty.revoked_commitment_penalty
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T22:52:26.002737+00:00
-- url     : https://prove2.me/theorems/7e9253b1-9993-4464-a300-9ca74b54e13c
-- title:
--   A revoked commitment transaction: every penalisable output is spendable at once by the holder of the revocation key
-- statement:
--   For a well-formed `K` and HTLC `h`, true programs, and `HoldsRevocation (oracleOf c sc) K` for every script `sc`: the `to_local` output and the offered and received HTLC outputs, in both the legacy and the anchors form, each have a penalty witness that `verifyScript` accepts, in one context. The BOLT #5 penalty transaction, output by output, at the script level.
-- source:
--   BOLT #3 (commitment transaction outputs, revocation) and BOLT #5 (penalty transactions): https://github.com/lightning/bolts/blob/master/03-transactions.md, https://github.com/lightning/bolts/blob/master/05-onchain.md#revoked-transaction-close-handling; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript, EvalScript, CheckSequence, IsFinalTx (src/script/interpreter.cpp, src/consensus/tx_verify.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinPenalty
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSer
open BitcoinPenalty BitcoinToLocal BitcoinHtlc BitcoinAnchors BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinPenalty.revoked_commitment_penalty (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (h : BitcoinPenalty.Htlc) (hw : BitcoinPenalty.HtlcWellFormed h)
    (hR : ∀ sc, BitcoinPenalty.HoldsRevocation (BitcoinPenalty.oracleOf c sc) K)
    (hh : ∀ sc ∈ [BitcoinPenalty.toLocalBytes K, BitcoinPenalty.offeredBytes K h, BitcoinPenalty.receivedBytes K h,
        BitcoinPenalty.offeredBytesAnchors K h, BitcoinPenalty.receivedBytesAnchors K h],
      BitcoinScript.castToBool (BitcoinSer.sha256 sc) = true) :
    (∃ sigR, BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.toLocalBytes K))
        (BitcoinPenalty.toLocalPenaltyWitness K sigR) = true) ∧
    (∃ sigR, BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.offeredBytes K h))
        (BitcoinPenalty.htlcPenaltyWitness K sigR (BitcoinPenalty.offeredBytes K h)) = true) ∧
    (∃ sigR, BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.receivedBytes K h))
        (BitcoinPenalty.htlcPenaltyWitness K sigR (BitcoinPenalty.receivedBytes K h)) = true) ∧
    (∃ sigR, BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.offeredBytesAnchors K h))
        (BitcoinPenalty.htlcPenaltyWitness K sigR (BitcoinPenalty.offeredBytesAnchors K h)) = true) ∧
    (∃ sigR, BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.receivedBytesAnchors K h))
        (BitcoinPenalty.htlcPenaltyWitness K sigR (BitcoinPenalty.receivedBytesAnchors K h)) = true) := by sorry
