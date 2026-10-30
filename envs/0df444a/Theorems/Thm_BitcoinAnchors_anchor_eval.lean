-- Prove2me | Theorems.Thm_BitcoinAnchors_anchor_eval
-- name    : BitcoinAnchors.anchor_eval
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T19:42:48.568958+00:00
-- url     : https://prove2.me/theorems/3c89f9c6-a02b-41fe-a873-fcfa8de23769
-- title:
--   Anchor on its witness, closed form
-- statement:
--   `evalScript f o [sig] (anchorScript k)` is `none` if the check rejects the signature's encoding, `some [[1]]` if it passes (`OP_IFDUP` keeps the true, `OP_NOTIF` skips the delay), and `if CsvPasses f o 16 then some [[16]] else none` if it returns a clean `false`.
-- source:
--   BOLT #3 with option_anchors: to_remote Output, Anchor Outputs, Offered/Received HTLC Outputs: https://github.com/lightning/bolts/blob/master/03-transactions.md#to_remote-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_CHECKSIGVERIFY, OP_IFDUP, OP_NOTIF, OP_CHECKSEQUENCEVERIFY, OP_CHECKMULTISIG), GenericTransactionSignatureChecker::CheckSequence (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinAnchors
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinToLocal
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinAnchors.anchor_eval (f : Flags) (o : Oracle) (fundingKey sig : Bytes)
    (hfk : fundingKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinScript.evalScript f o [sig] (BitcoinAnchors.anchorScript fundingKey) =
      match o.checkSig sig fundingKey with
      | none => none
      | some true => some [[1]]
      | some false => if BitcoinToLocal.CsvPasses f o 16 then some [[16]] else none := by sorry
