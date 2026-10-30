-- Prove2me | Theorems.Thm_BitcoinPenalty_to_local_penalty
-- name    : BitcoinPenalty.to_local_penalty
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T22:51:28.449431+00:00
-- url     : https://prove2.me/theorems/98957868-03f2-406a-92f8-5beb301a73c8
-- title:
--   to_local penalty: the holder of the revocation key spends the balance output
-- statement:
--   Under `HoldsRevocation (oracleOf c (toLocalBytes K)) K` there is a `sigR` whose penalty witness `verifyScript` accepts.
-- source:
--   BOLT #3 (commitment transaction outputs, revocation) and BOLT #5 (penalty transactions): https://github.com/lightning/bolts/blob/master/03-transactions.md, https://github.com/lightning/bolts/blob/master/05-onchain.md#revoked-transaction-close-handling; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript, EvalScript, CheckSequence, IsFinalTx (src/script/interpreter.cpp, src/consensus/tx_verify.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinPenalty
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSer
open BitcoinPenalty BitcoinToLocal BitcoinHtlc BitcoinAnchors BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinPenalty.to_local_penalty (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (hh : BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinPenalty.toLocalBytes K)) = true)
    (hR : BitcoinPenalty.HoldsRevocation (BitcoinPenalty.oracleOf c (BitcoinPenalty.toLocalBytes K)) K) :
    ∃ sigR, BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.toLocalBytes K))
      (BitcoinPenalty.toLocalPenaltyWitness K sigR) = true := by sorry
