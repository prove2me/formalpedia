-- Prove2me | Theorems.Thm_BitcoinAnchors_anchor_p2wsh_spend
-- name    : BitcoinAnchors.anchor_p2wsh_spend
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T20:16:39.722083+00:00
-- url     : https://prove2.me/theorems/a5944448-5c5a-4282-80db-63c1fa8b9c17
-- title:
--   The anchor output under VerifyScript
-- statement:
--   As above with `AnchorSpend`: the anchor is spent by the funding-key holder at any time, or by anyone with a clean-false signature after the delay.
-- source:
--   BOLT #3 with option_anchors: to_remote Output, Anchor Outputs, Offered/Received HTLC Outputs: https://github.com/lightning/bolts/blob/master/03-transactions.md#to_remote-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_CHECKSIGVERIFY, OP_IFDUP, OP_NOTIF, OP_CHECKSEQUENCEVERIFY, OP_CHECKMULTISIG), GenericTransactionSignatureChecker::CheckSequence (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinAnchors
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinSig
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinAnchors.anchor_p2wsh_spend (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (fundingKey : Bytes) (ws : List Bytes)
    (hfk : fundingKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinVerify.verifyScript tap c []
        (BitcoinVerify.witnessBytes 0 (BitcoinSer.sha256 (BitcoinAnchors.anchorBytes fundingKey)))
        (ws ++ [BitcoinAnchors.anchorBytes fundingKey]) = true ↔
      BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinAnchors.anchorBytes fundingKey)) = true ∧
      (∀ e ∈ ws, e.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) ∧
      BitcoinAnchors.AnchorSpend (BitcoinVerify.scriptFlagsOf c.flags)
        (BitcoinSig.legacyOracle (BitcoinVerify.sigFlagsOf c.flags) c.tx c.nIn c.amount .witnessV0
          (BitcoinAnchors.anchorBytes fundingKey))
        fundingKey ws.reverse := by sorry
