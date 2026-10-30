-- Prove2me | Theorems.Thm_BitcoinAnchors_to_remote_eval
-- name    : BitcoinAnchors.to_remote_eval
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T19:42:19.050635+00:00
-- url     : https://prove2.me/theorems/d4dd7497-b4d9-4e7b-9207-19eadacffe15
-- title:
--   to_remote on its witness
-- statement:
--   `evalScript f o [sig] (toRemoteScript k) = if o.checkSig sig k = some true ∧ CsvPasses f o 1 then some [[1]] else none`.
-- source:
--   BOLT #3 with option_anchors: to_remote Output, Anchor Outputs, Offered/Received HTLC Outputs: https://github.com/lightning/bolts/blob/master/03-transactions.md#to_remote-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_CHECKSIGVERIFY, OP_IFDUP, OP_NOTIF, OP_CHECKSEQUENCEVERIFY, OP_CHECKMULTISIG), GenericTransactionSignatureChecker::CheckSequence (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinAnchors
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinToLocal
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinAnchors.to_remote_eval (f : Flags) (o : Oracle) (remoteKey sig : Bytes)
    (hrem : remoteKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinScript.evalScript f o [sig] (BitcoinAnchors.toRemoteScript remoteKey) =
      if o.checkSig sig remoteKey = some true ∧ BitcoinToLocal.CsvPasses f o 1 then some [[1]] else none := by sorry
