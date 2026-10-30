-- Prove2me | Theorems.Thm_BitcoinAnchors_anchor_anyone
-- name    : BitcoinAnchors.anchor_anyone
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T19:43:31.915705+00:00
-- url     : https://prove2.me/theorems/8092b2ed-5f6e-4e9b-9dff-779e1beb2ddd
-- title:
--   Anchor, anyone-can-spend path
-- statement:
--   If `o.checkSig sig k = some false` then `evalScript f o [sig] (anchorScript k) = if CsvPasses f o 16 then some [[16]] else none`: with a clean false (the empty signature), the anchor is spendable exactly after the 16-block delay.
-- source:
--   BOLT #3 with option_anchors: to_remote Output, Anchor Outputs, Offered/Received HTLC Outputs: https://github.com/lightning/bolts/blob/master/03-transactions.md#to_remote-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_CHECKSIGVERIFY, OP_IFDUP, OP_NOTIF, OP_CHECKSEQUENCEVERIFY, OP_CHECKMULTISIG), GenericTransactionSignatureChecker::CheckSequence (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinAnchors
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinToLocal
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinAnchors.anchor_anyone (f : Flags) (o : Oracle) (fundingKey sig : Bytes)
    (hfk : fundingKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hcs : o.checkSig sig fundingKey = some false) :
    BitcoinScript.evalScript f o [sig] (BitcoinAnchors.anchorScript fundingKey) =
      if BitcoinToLocal.CsvPasses f o 16 then some [[16]] else none := by sorry
