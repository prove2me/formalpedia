-- Prove2me | Theorems.Thm_BitcoinAnchors_parseScript_received
-- name    : BitcoinAnchors.parseScript_received
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T20:16:14.505285+00:00
-- url     : https://prove2.me/theorems/034a146f-2852-4dd3-8498-3f97916def44
-- title:
--   Received HTLC (anchors) byte form parses
-- statement:
--   For pushed strings of at most 520 bytes and $|{\rm expiry}| < 2^{32}$: `parseScript (receivedBytes …) = some (receivedScript …)`.
-- source:
--   BOLT #3 with option_anchors: to_remote Output, Anchor Outputs, Offered/Received HTLC Outputs: https://github.com/lightning/bolts/blob/master/03-transactions.md#to_remote-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_CHECKSIGVERIFY, OP_IFDUP, OP_NOTIF, OP_CHECKSEQUENCEVERIFY, OP_CHECKMULTISIG), GenericTransactionSignatureChecker::CheckSequence (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinAnchors
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSig
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinAnchors.parseScript_received (revHash remoteKey localKey payHash : Bytes) (expiry : Int)
    (hrev : revHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hrem : remoteKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hloc : localKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hd : expiry.natAbs < 2 ^ 32) :
    BitcoinSig.parseScript (BitcoinAnchors.receivedBytes revHash remoteKey localKey payHash expiry) =
      some (BitcoinAnchors.receivedScript revHash remoteKey localKey payHash expiry) := by sorry
