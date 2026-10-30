-- Prove2me | Theorems.Thm_BitcoinPenalty_received_htlc_penalty_anchors
-- name    : BitcoinPenalty.received_htlc_penalty_anchors
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T22:52:13.177602+00:00
-- url     : https://prove2.me/theorems/eb4749ae-eecc-4a53-b113-650fcf84aa2b
-- title:
--   Received HTLC penalty, anchors form
-- statement:
--   As `received_htlc_penalty` for the anchors-form script.
-- source:
--   BOLT #3 (commitment transaction outputs, revocation) and BOLT #5 (penalty transactions): https://github.com/lightning/bolts/blob/master/03-transactions.md, https://github.com/lightning/bolts/blob/master/05-onchain.md#revoked-transaction-close-handling; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript, EvalScript, CheckSequence, IsFinalTx (src/script/interpreter.cpp, src/consensus/tx_verify.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinPenalty
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSer
open BitcoinPenalty BitcoinToLocal BitcoinHtlc BitcoinAnchors BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinPenalty.received_htlc_penalty_anchors (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (h : BitcoinPenalty.Htlc) (hw : BitcoinPenalty.HtlcWellFormed h)
    (hh : BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinPenalty.receivedBytesAnchors K h)) = true)
    (hR : BitcoinPenalty.HoldsRevocation (BitcoinPenalty.oracleOf c (BitcoinPenalty.receivedBytesAnchors K h)) K) :
    ∃ sigR, BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.receivedBytesAnchors K h))
      (BitcoinPenalty.htlcPenaltyWitness K sigR (BitcoinPenalty.receivedBytesAnchors K h)) = true := by sorry
