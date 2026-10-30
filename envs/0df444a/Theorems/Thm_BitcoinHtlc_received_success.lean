-- Prove2me | Theorems.Thm_BitcoinHtlc_received_success
-- name    : BitcoinHtlc.received_success
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T17:27:37.635313+00:00
-- url     : https://prove2.me/theorems/0526c334-2604-4142-ab93-aebe53646c52
-- title:
--   Received HTLC, success path (preimage and 2-of-2)
-- statement:
--   For pushed strings of at most 520 bytes, $|{\rm expiry}| < 2^{32}$, `hash160 preimage ≠ revHash` and a 32-byte preimage: on `[preimage, localSig, remoteSig, dummy]` the script fails unless `hash160 preimage = payHash`, then behaves as the offered timeout path's 2-of-2 check.
-- source:
--   BOLT #3, Bitcoin Transaction and Script Formats, 'Offered HTLC Outputs' and 'Received HTLC Outputs': https://github.com/lightning/bolts/blob/master/03-transactions.md#offered-htlc-outputs; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_DUP, OP_HASH160, OP_EQUAL, OP_IF/OP_NOTIF, OP_SWAP, OP_SIZE, OP_CHECKMULTISIG, OP_CHECKLOCKTIMEVERIFY, OP_CHECKSIG), GenericTransactionSignatureChecker::CheckLockTime (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP65, BIP141, BIP147

import Definitions.Def_BitcoinHtlc
import Definitions.Def_BitcoinScript
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinHtlc.received_success (f : Flags) (o : Oracle) (revHash remoteKey localKey payHash preimage localSig remoteSig dummy : Bytes)
    (expiry : Int)
    (hrev : revHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hrem : remoteKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hloc : localKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hd : expiry.natAbs < 2 ^ 32) (hb : o.hash160 preimage ≠ revHash) (h32 : preimage.length = 32) :
    BitcoinScript.evalScript f o [preimage, localSig, remoteSig, dummy]
        (BitcoinHtlc.receivedScript revHash remoteKey localKey payHash expiry) =
      if o.hash160 preimage = payHash then
        match BitcoinScript.multisigLoop o [localSig, remoteSig] [localKey, remoteKey] with
        | none => none
        | some ok => if f.nulldummy && !dummy.isEmpty then none else some [BitcoinScript.boolBytes ok]
      else none := by sorry
