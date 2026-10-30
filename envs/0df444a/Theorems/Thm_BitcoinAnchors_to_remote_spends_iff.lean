-- Prove2me | Theorems.Thm_BitcoinAnchors_to_remote_spends_iff
-- name    : BitcoinAnchors.to_remote_spends_iff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T19:42:34.58183+00:00
-- url     : https://prove2.me/theorems/5444e379-8ce2-4e07-a183-0493b8b8124f
-- title:
--   to_remote: the spending condition, for any witness stack
-- statement:
--   For pushed strings of at most 520 bytes and any stack `st`: the witness-v0 success condition for `toRemoteScript remoteKey` holds iff `ToRemoteSpend f o remoteKey st`. `OP_CHECKSIGVERIFY` fails the script on anything but a passing check; the `1` pushed for the delay is the value left.
-- source:
--   BOLT #3 with option_anchors: to_remote Output, Anchor Outputs, Offered/Received HTLC Outputs: https://github.com/lightning/bolts/blob/master/03-transactions.md#to_remote-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_CHECKSIGVERIFY, OP_IFDUP, OP_NOTIF, OP_CHECKSEQUENCEVERIFY, OP_CHECKMULTISIG), GenericTransactionSignatureChecker::CheckSequence (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinAnchors
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinVerify
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinAnchors.to_remote_spends_iff (f : Flags) (o : Oracle) (remoteKey : Bytes) (st : List Bytes)
    (hrem : remoteKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    (∃ res, BitcoinScript.evalScript f o st (BitcoinAnchors.toRemoteScript remoteKey) = some res ∧
        res.length = 1 ∧ BitcoinVerify.topTrue res = true) ↔
      BitcoinAnchors.ToRemoteSpend f o remoteKey st := by sorry
