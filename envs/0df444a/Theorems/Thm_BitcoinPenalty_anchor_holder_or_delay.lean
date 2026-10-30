-- Prove2me | Theorems.Thm_BitcoinPenalty_anchor_holder_or_delay
-- name    : BitcoinPenalty.anchor_holder_or_delay
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T22:52:57.018086+00:00
-- url     : https://prove2.me/theorems/9ef75651-a3eb-4552-946d-ead5a0ec04f6
-- title:
--   Anchors: the funding-key holder at any time, anyone after the delay
-- statement:
--   For either anchor: accepted witnesses are `[sig]` with `sig` valid for the funding key, or a clean false together with `CsvPasses … 16`.
-- source:
--   BOLT #3 (commitment transaction outputs, revocation) and BOLT #5 (penalty transactions): https://github.com/lightning/bolts/blob/master/03-transactions.md, https://github.com/lightning/bolts/blob/master/05-onchain.md#revoked-transaction-close-handling; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript, EvalScript, CheckSequence, IsFinalTx (src/script/interpreter.cpp, src/consensus/tx_verify.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinPenalty
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinAnchors
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinToLocal
open BitcoinPenalty BitcoinToLocal BitcoinHtlc BitcoinAnchors BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinPenalty.anchor_holder_or_delay (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (fk : BitcoinSer.Bytes) (hfk : fk = K.fundingKeyLocal ∨ fk = K.fundingKeyRemote) (ws : List BitcoinSer.Bytes) :
    BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinAnchors.anchorBytes fk))
        (ws ++ [BitcoinAnchors.anchorBytes fk]) = true ↔
      BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinAnchors.anchorBytes fk)) = true ∧
      (∀ e ∈ ws, e.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) ∧
      ∃ sig, ws = [sig] ∧
        ((BitcoinPenalty.oracleOf c (BitcoinAnchors.anchorBytes fk)).checkSig sig fk = some true ∨
          ((BitcoinPenalty.oracleOf c (BitcoinAnchors.anchorBytes fk)).checkSig sig fk = some false ∧
            BitcoinToLocal.CsvPasses (BitcoinVerify.scriptFlagsOf c.flags)
              (BitcoinPenalty.oracleOf c (BitcoinAnchors.anchorBytes fk)) 16)) := by sorry
