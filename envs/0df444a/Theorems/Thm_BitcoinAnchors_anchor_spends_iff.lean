-- Prove2me | Theorems.Thm_BitcoinAnchors_anchor_spends_iff
-- name    : BitcoinAnchors.anchor_spends_iff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T19:43:55.70221+00:00
-- url     : https://prove2.me/theorems/158ee7a3-be01-40e4-9cae-2fcbd9a55660
-- title:
--   Anchor: the two spending conditions, for any witness stack
-- statement:
--   For pushed strings of at most 520 bytes and any stack: the success condition for `anchorScript fundingKey` holds iff `AnchorSpend f o fundingKey st`.
-- source:
--   BOLT #3 with option_anchors: to_remote Output, Anchor Outputs, Offered/Received HTLC Outputs: https://github.com/lightning/bolts/blob/master/03-transactions.md#to_remote-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_CHECKSIGVERIFY, OP_IFDUP, OP_NOTIF, OP_CHECKSEQUENCEVERIFY, OP_CHECKMULTISIG), GenericTransactionSignatureChecker::CheckSequence (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinAnchors
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinVerify
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinAnchors.anchor_spends_iff (f : Flags) (o : Oracle) (fundingKey : Bytes) (st : List Bytes)
    (hfk : fundingKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    (∃ res, BitcoinScript.evalScript f o st (BitcoinAnchors.anchorScript fundingKey) = some res ∧
        res.length = 1 ∧ BitcoinVerify.topTrue res = true) ↔
      BitcoinAnchors.AnchorSpend f o fundingKey st := by sorry
