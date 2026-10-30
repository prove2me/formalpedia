-- Prove2me | Theorems.Thm_BitcoinAnchors_anchor_holder
-- name    : BitcoinAnchors.anchor_holder
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T19:43:08.716227+00:00
-- url     : https://prove2.me/theorems/ed7a3ff0-4174-4617-b2ca-7e1251709e01
-- title:
--   Anchor, key-holder path
-- statement:
--   If `o.checkSig sig k = some true` then `evalScript f o [sig] (anchorScript k) = some [[1]]`: the funding-key holder spends the anchor at any time.
-- source:
--   BOLT #3 with option_anchors: to_remote Output, Anchor Outputs, Offered/Received HTLC Outputs: https://github.com/lightning/bolts/blob/master/03-transactions.md#to_remote-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_CHECKSIGVERIFY, OP_IFDUP, OP_NOTIF, OP_CHECKSEQUENCEVERIFY, OP_CHECKMULTISIG), GenericTransactionSignatureChecker::CheckSequence (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinAnchors
import Definitions.Def_BitcoinScript
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinAnchors.anchor_holder (f : Flags) (o : Oracle) (fundingKey sig : Bytes)
    (hfk : fundingKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hcs : o.checkSig sig fundingKey = some true) :
    BitcoinScript.evalScript f o [sig] (BitcoinAnchors.anchorScript fundingKey) = some [[1]] := by sorry
