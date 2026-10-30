-- Prove2me | Theorems.Thm_BitcoinAnchors_received_spends_iff
-- name    : BitcoinAnchors.received_spends_iff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T20:15:25.617732+00:00
-- url     : https://prove2.me/theorems/6806785d-12a6-4de3-94e9-981347202d5d
-- title:
--   Received HTLC (anchors): the three spending conditions, for any witness stack
-- statement:
--   For pushed strings of at most 520 bytes, $|{\rm expiry}| < 2^{32}$ and any stack: the success condition holds iff `ReceivedSpend f o … expiry st`.
-- source:
--   BOLT #3 with option_anchors: to_remote Output, Anchor Outputs, Offered/Received HTLC Outputs: https://github.com/lightning/bolts/blob/master/03-transactions.md#to_remote-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_CHECKSIGVERIFY, OP_IFDUP, OP_NOTIF, OP_CHECKSEQUENCEVERIFY, OP_CHECKMULTISIG), GenericTransactionSignatureChecker::CheckSequence (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinAnchors
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinVerify
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinAnchors.received_spends_iff (f : Flags) (o : Oracle) (revHash remoteKey localKey payHash : Bytes) (expiry : Int)
    (st : List Bytes)
    (hrev : revHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hrem : remoteKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hloc : localKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hd : expiry.natAbs < 2 ^ 32) :
    (∃ res, BitcoinScript.evalScript f o st (BitcoinAnchors.receivedScript revHash remoteKey localKey payHash expiry) = some res ∧
        res.length = 1 ∧ BitcoinVerify.topTrue res = true) ↔
      BitcoinAnchors.ReceivedSpend f o revHash remoteKey localKey payHash expiry st := by sorry
