-- Prove2me | Theorems.Thm_BitcoinAnchors_offered_revocation
-- name    : BitcoinAnchors.offered_revocation
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T19:44:16.507773+00:00
-- url     : https://prove2.me/theorems/515544a0-b800-4b41-8b15-ea50a21b91b3
-- title:
--   Offered HTLC (anchors), revocation path
-- statement:
--   As the HTLC mission's: the revocation branch skips the delay suffix.
-- source:
--   BOLT #3 with option_anchors: to_remote Output, Anchor Outputs, Offered/Received HTLC Outputs: https://github.com/lightning/bolts/blob/master/03-transactions.md#to_remote-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_CHECKSIGVERIFY, OP_IFDUP, OP_NOTIF, OP_CHECKSEQUENCEVERIFY, OP_CHECKMULTISIG), GenericTransactionSignatureChecker::CheckSequence (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinAnchors
import Definitions.Def_BitcoinScript
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinAnchors.offered_revocation (f : Flags) (o : Oracle) (revHash remoteKey localKey payHash pk sig : Bytes)
    (hrev : revHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hrem : remoteKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hloc : localKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hb : o.hash160 pk = revHash) :
    BitcoinScript.evalScript f o [pk, sig] (BitcoinAnchors.offeredScript revHash remoteKey localKey payHash) =
      (o.checkSig sig pk).map (fun ok => [BitcoinScript.boolBytes ok]) := by sorry
