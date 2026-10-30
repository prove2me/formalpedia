-- Prove2me | Theorems.Thm_BitcoinAnchors_parseScript_toRemote
-- name    : BitcoinAnchors.parseScript_toRemote
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T20:15:35.897096+00:00
-- url     : https://prove2.me/theorems/354316f2-e852-490a-ba1c-068d28fab115
-- title:
--   to_remote byte form parses
-- statement:
--   `parseScript (toRemoteBytes k) = some (toRemoteScript k)` for a key of at most 520 bytes.
-- source:
--   BOLT #3 with option_anchors: to_remote Output, Anchor Outputs, Offered/Received HTLC Outputs: https://github.com/lightning/bolts/blob/master/03-transactions.md#to_remote-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_CHECKSIGVERIFY, OP_IFDUP, OP_NOTIF, OP_CHECKSEQUENCEVERIFY, OP_CHECKMULTISIG), GenericTransactionSignatureChecker::CheckSequence (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinAnchors
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSig
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinAnchors.parseScript_toRemote (remoteKey : Bytes) (hrem : remoteKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinSig.parseScript (BitcoinAnchors.toRemoteBytes remoteKey) = some (BitcoinAnchors.toRemoteScript remoteKey) := by sorry
