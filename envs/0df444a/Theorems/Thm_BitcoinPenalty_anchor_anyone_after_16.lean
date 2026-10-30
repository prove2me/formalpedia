-- Prove2me | Theorems.Thm_BitcoinPenalty_anchor_anyone_after_16
-- name    : BitcoinPenalty.anchor_anyone_after_16
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T22:53:11.039592+00:00
-- url     : https://prove2.me/theorems/d7b63793-47fa-4bd8-86c3-4e66d8310f10
-- title:
--   Anchors: the empty-signature sweep in transaction terms
-- statement:
--   With the `CSV` flag and flag-free `nSequence`: `[[], anchorBytes fk]` verifies iff the program is true, the version is at least 2 and `nSequence ≥ 16`.
-- source:
--   BOLT #3 (commitment transaction outputs, revocation) and BOLT #5 (penalty transactions): https://github.com/lightning/bolts/blob/master/03-transactions.md, https://github.com/lightning/bolts/blob/master/05-onchain.md#revoked-transaction-close-handling; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript, EvalScript, CheckSequence, IsFinalTx (src/script/interpreter.cpp, src/consensus/tx_verify.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinPenalty
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinToLocal
import Definitions.Def_BitcoinAnchors
import Definitions.Def_BitcoinScript
open BitcoinPenalty BitcoinToLocal BitcoinHtlc BitcoinAnchors BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinPenalty.anchor_anyone_after_16 (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (hcsv : c.flags.csv = true) (K : BitcoinPenalty.CommitmentKeys)
    (hK : BitcoinPenalty.WellFormed K) (fk : BitcoinSer.Bytes) (hfk : fk = K.fundingKeyLocal ∨ fk = K.fundingKeyRemote)
    (hseq : BitcoinToLocal.inputSequence c.tx c.nIn < 2 ^ 16) :
    BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinAnchors.anchorBytes fk))
        [[], BitcoinAnchors.anchorBytes fk] = true ↔
      BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinAnchors.anchorBytes fk)) = true ∧
      2 ≤ c.tx.version ∧ 16 ≤ BitcoinToLocal.inputSequence c.tx c.nIn := by sorry
