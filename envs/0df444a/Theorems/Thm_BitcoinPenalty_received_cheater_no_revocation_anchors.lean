-- Prove2me | Theorems.Thm_BitcoinPenalty_received_cheater_no_revocation_anchors
-- name    : BitcoinPenalty.received_cheater_no_revocation_anchors
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T22:55:14.244734+00:00
-- url     : https://prove2.me/theorems/dd2d089a-6e7d-4fef-963a-cf741a7aa8ca
-- title:
--   Received HTLC safety, anchors form
-- statement:
--   As above with the one-block delay in every path.
-- source:
--   BOLT #3 (commitment transaction outputs, revocation) and BOLT #5 (penalty transactions): https://github.com/lightning/bolts/blob/master/03-transactions.md, https://github.com/lightning/bolts/blob/master/05-onchain.md#revoked-transaction-close-handling; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript, EvalScript, CheckSequence, IsFinalTx (src/script/interpreter.cpp, src/consensus/tx_verify.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinPenalty
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinSer
open BitcoinPenalty BitcoinToLocal BitcoinHtlc BitcoinAnchors BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinPenalty.received_cheater_no_revocation_anchors (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (h : BitcoinPenalty.Htlc) (hw : BitcoinPenalty.HtlcWellFormed h)
    (hN : BitcoinPenalty.NoRevocationSig (BitcoinPenalty.oracleOf c (BitcoinPenalty.receivedBytesAnchors K h)) K)
    (hP : BitcoinPenalty.NoRevHashPreimage (BitcoinPenalty.oracleOf c (BitcoinPenalty.receivedBytesAnchors K h)) K)
    (ws : List BitcoinSer.Bytes)
    (hv : BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.receivedBytesAnchors K h))
      (ws ++ [BitcoinPenalty.receivedBytesAnchors K h]) = true) :
    BitcoinPenalty.ReceivedNonRevocationAnchors (BitcoinVerify.scriptFlagsOf c.flags)
      (BitcoinPenalty.oracleOf c (BitcoinPenalty.receivedBytesAnchors K h)) K h ws.reverse := by sorry
