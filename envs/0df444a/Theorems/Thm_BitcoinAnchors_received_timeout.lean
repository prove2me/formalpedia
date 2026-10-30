-- Prove2me | Theorems.Thm_BitcoinAnchors_received_timeout
-- name    : BitcoinAnchors.received_timeout
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T20:15:06.292177+00:00
-- url     : https://prove2.me/theorems/e3fbfc20-beb7-4947-90d2-6d051ea59361
-- title:
--   Received HTLC (anchors), timeout path
-- statement:
--   For pushed strings of at most 520 bytes, `hash160 x ≠ revHash`, `x` not 32 bytes: `if CltvPasses f o expiry ∧ CsvPasses f o 1 then (checkSig sig remoteKey).map … else none`.
-- source:
--   BOLT #3 with option_anchors: to_remote Output, Anchor Outputs, Offered/Received HTLC Outputs: https://github.com/lightning/bolts/blob/master/03-transactions.md#to_remote-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_CHECKSIGVERIFY, OP_IFDUP, OP_NOTIF, OP_CHECKSEQUENCEVERIFY, OP_CHECKMULTISIG), GenericTransactionSignatureChecker::CheckSequence (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinAnchors
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinHtlc
import Definitions.Def_BitcoinToLocal
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinAnchors.received_timeout (f : Flags) (o : Oracle) (revHash remoteKey localKey payHash x sig : Bytes) (expiry : Int)
    (hrev : revHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hrem : remoteKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hloc : localKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hd : expiry.natAbs < 2 ^ 32) (hb : o.hash160 x ≠ revHash) (h32 : x.length ≠ 32) :
    BitcoinScript.evalScript f o [x, sig] (BitcoinAnchors.receivedScript revHash remoteKey localKey payHash expiry) =
      if BitcoinHtlc.CltvPasses f o expiry ∧ BitcoinToLocal.CsvPasses f o 1 then
        (o.checkSig sig remoteKey).map (fun ok => [BitcoinScript.boolBytes ok])
      else none := by sorry
