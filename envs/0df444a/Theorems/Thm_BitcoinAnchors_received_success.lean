-- Prove2me | Theorems.Thm_BitcoinAnchors_received_success
-- name    : BitcoinAnchors.received_success
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T20:14:51.178242+00:00
-- url     : https://prove2.me/theorems/38068bd3-8eca-4fff-ad21-733de517dd49
-- title:
--   Received HTLC (anchors), success path
-- statement:
--   For pushed strings of at most 520 bytes, $|{\rm expiry}| < 2^{32}$, 32-byte preimage not hashing to `revHash`: `if hash160 preimage = payHash ∧ CsvPasses f o 1 then` the 2-of-2 result `else none`.
-- source:
--   BOLT #3 with option_anchors: to_remote Output, Anchor Outputs, Offered/Received HTLC Outputs: https://github.com/lightning/bolts/blob/master/03-transactions.md#to_remote-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_CHECKSIGVERIFY, OP_IFDUP, OP_NOTIF, OP_CHECKSEQUENCEVERIFY, OP_CHECKMULTISIG), GenericTransactionSignatureChecker::CheckSequence (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinAnchors
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinToLocal
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinAnchors.received_success (f : Flags) (o : Oracle) (revHash remoteKey localKey payHash preimage localSig remoteSig dummy : Bytes)
    (expiry : Int)
    (hrev : revHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hrem : remoteKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hloc : localKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hd : expiry.natAbs < 2 ^ 32) (hb : o.hash160 preimage ≠ revHash) (h32 : preimage.length = 32) :
    BitcoinScript.evalScript f o [preimage, localSig, remoteSig, dummy]
        (BitcoinAnchors.receivedScript revHash remoteKey localKey payHash expiry) =
      if o.hash160 preimage = payHash ∧ BitcoinToLocal.CsvPasses f o 1 then
        match BitcoinScript.multisigLoop o [localSig, remoteSig] [localKey, remoteKey] with
        | none => none
        | some ok => if f.nulldummy && !dummy.isEmpty then none else some [BitcoinScript.boolBytes ok]
      else none := by sorry
