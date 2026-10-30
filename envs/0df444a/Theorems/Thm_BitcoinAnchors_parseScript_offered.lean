-- Prove2me | Theorems.Thm_BitcoinAnchors_parseScript_offered
-- name    : BitcoinAnchors.parseScript_offered
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T20:16:02.504+00:00
-- url     : https://prove2.me/theorems/6864735d-b8b9-479d-a3cf-4df996a115ed
-- title:
--   Offered HTLC (anchors) byte form parses
-- statement:
--   For pushed strings of at most 520 bytes: `parseScript (offeredBytes …) = some (offeredScript …)`.
-- source:
--   BOLT #3 with option_anchors: to_remote Output, Anchor Outputs, Offered/Received HTLC Outputs: https://github.com/lightning/bolts/blob/master/03-transactions.md#to_remote-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_CHECKSIGVERIFY, OP_IFDUP, OP_NOTIF, OP_CHECKSEQUENCEVERIFY, OP_CHECKMULTISIG), GenericTransactionSignatureChecker::CheckSequence (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinAnchors
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSig
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinAnchors.parseScript_offered (revHash remoteKey localKey payHash : Bytes)
    (hrev : revHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hrem : remoteKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hloc : localKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinSig.parseScript (BitcoinAnchors.offeredBytes revHash remoteKey localKey payHash) =
      some (BitcoinAnchors.offeredScript revHash remoteKey localKey payHash) := by sorry
