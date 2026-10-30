-- Prove2me | Theorems.Thm_BitcoinPenalty_offered_cheater_no_revocation
-- name    : BitcoinPenalty.offered_cheater_no_revocation
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T22:54:25.705974+00:00
-- url     : https://prove2.me/theorems/99bdff58-0e7d-4c55-9205-f05f34fa6396
-- title:
--   Offered HTLC safety: the cheater never takes the revocation path
-- statement:
--   Under `NoRevocationSig` and `NoRevHashPreimage`: every accepted spend of the offered HTLC is a preimage or timeout path (`OfferedNonRevocation`).
-- source:
--   BOLT #3 (commitment transaction outputs, revocation) and BOLT #5 (penalty transactions): https://github.com/lightning/bolts/blob/master/03-transactions.md, https://github.com/lightning/bolts/blob/master/05-onchain.md#revoked-transaction-close-handling; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript, EvalScript, CheckSequence, IsFinalTx (src/script/interpreter.cpp, src/consensus/tx_verify.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinPenalty
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinSer
open BitcoinPenalty BitcoinToLocal BitcoinHtlc BitcoinAnchors BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinPenalty.offered_cheater_no_revocation (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (h : BitcoinPenalty.Htlc) (hw : BitcoinPenalty.HtlcWellFormed h)
    (hN : BitcoinPenalty.NoRevocationSig (BitcoinPenalty.oracleOf c (BitcoinPenalty.offeredBytes K h)) K)
    (hP : BitcoinPenalty.NoRevHashPreimage (BitcoinPenalty.oracleOf c (BitcoinPenalty.offeredBytes K h)) K)
    (ws : List BitcoinSer.Bytes)
    (hv : BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.offeredBytes K h))
      (ws ++ [BitcoinPenalty.offeredBytes K h]) = true) :
    BitcoinPenalty.OfferedNonRevocation (BitcoinVerify.scriptFlagsOf c.flags)
      (BitcoinPenalty.oracleOf c (BitcoinPenalty.offeredBytes K h)) K h ws.reverse := by sorry
