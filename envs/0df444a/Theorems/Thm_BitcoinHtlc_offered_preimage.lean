-- Prove2me | Theorems.Thm_BitcoinHtlc_offered_preimage
-- name    : BitcoinHtlc.offered_preimage
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T17:26:43.955851+00:00
-- url     : https://prove2.me/theorems/676ce72d-f1cc-44f9-bed7-d2e6b5f2171d
-- title:
--   Offered HTLC, preimage path
-- statement:
--   For pushed strings of at most 520 bytes, `hash160 preimage ≠ revHash` and a 32-byte preimage: the script leaves the remote-key signature check if `hash160 preimage = payHash`, and fails otherwise.
-- source:
--   BOLT #3, Bitcoin Transaction and Script Formats, 'Offered HTLC Outputs' and 'Received HTLC Outputs': https://github.com/lightning/bolts/blob/master/03-transactions.md#offered-htlc-outputs; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_DUP, OP_HASH160, OP_EQUAL, OP_IF/OP_NOTIF, OP_SWAP, OP_SIZE, OP_CHECKMULTISIG, OP_CHECKLOCKTIMEVERIFY, OP_CHECKSIG), GenericTransactionSignatureChecker::CheckLockTime (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP65, BIP141, BIP147

import Definitions.Def_BitcoinHtlc
import Definitions.Def_BitcoinScript
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinHtlc.offered_preimage (f : Flags) (o : Oracle) (revHash remoteKey localKey payHash preimage sig : Bytes)
    (hrev : revHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hrem : remoteKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hloc : localKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hb : o.hash160 preimage ≠ revHash) (h32 : preimage.length = 32) :
    BitcoinScript.evalScript f o [preimage, sig] (BitcoinHtlc.offeredScript revHash remoteKey localKey payHash) =
      if o.hash160 preimage = payHash then (o.checkSig sig remoteKey).map (fun ok => [BitcoinScript.boolBytes ok]) else none := by sorry
