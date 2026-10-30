-- Prove2me | Theorems.Thm_BitcoinAnchors_offered_preimage
-- name    : BitcoinAnchors.offered_preimage
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T19:44:37.983407+00:00
-- url     : https://prove2.me/theorems/90cd902b-cd38-4594-b06e-986db223f86c
-- title:
--   Offered HTLC (anchors), preimage path
-- statement:
--   For pushed strings of at most 520 bytes, `hash160 preimage ≠ revHash`, 32-byte preimage: `if hash160 preimage = payHash ∧ CsvPasses f o 1 then (checkSig sig remoteKey).map … else none`.
-- source:
--   BOLT #3 with option_anchors: to_remote Output, Anchor Outputs, Offered/Received HTLC Outputs: https://github.com/lightning/bolts/blob/master/03-transactions.md#to_remote-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_CHECKSIGVERIFY, OP_IFDUP, OP_NOTIF, OP_CHECKSEQUENCEVERIFY, OP_CHECKMULTISIG), GenericTransactionSignatureChecker::CheckSequence (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinAnchors
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinToLocal
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinAnchors.offered_preimage (f : Flags) (o : Oracle) (revHash remoteKey localKey payHash preimage sig : Bytes)
    (hrev : revHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hrem : remoteKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hloc : localKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hb : o.hash160 preimage ≠ revHash) (h32 : preimage.length = 32) :
    BitcoinScript.evalScript f o [preimage, sig] (BitcoinAnchors.offeredScript revHash remoteKey localKey payHash) =
      if o.hash160 preimage = payHash ∧ BitcoinToLocal.CsvPasses f o 1 then
        (o.checkSig sig remoteKey).map (fun ok => [BitcoinScript.boolBytes ok])
      else none := by sorry
