-- Prove2me | Theorems.Thm_BitcoinHtlc_offered_timeout
-- name    : BitcoinHtlc.offered_timeout
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T17:26:58.493688+00:00
-- url     : https://prove2.me/theorems/62c64d5b-c24d-484b-8d0a-25be0470e0da
-- title:
--   Offered HTLC, timeout path (2-of-2)
-- statement:
--   For pushed strings of at most 520 bytes, `hash160 x ≠ revHash` and `x` not 32 bytes: on `[x, localSig, remoteSig, dummy]` the script fails if the 2-of-2 loop errors, fails if `NULLDUMMY` is on and the dummy is nonempty, and otherwise leaves the loop's verdict.
-- source:
--   BOLT #3, Bitcoin Transaction and Script Formats, 'Offered HTLC Outputs' and 'Received HTLC Outputs': https://github.com/lightning/bolts/blob/master/03-transactions.md#offered-htlc-outputs; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_DUP, OP_HASH160, OP_EQUAL, OP_IF/OP_NOTIF, OP_SWAP, OP_SIZE, OP_CHECKMULTISIG, OP_CHECKLOCKTIMEVERIFY, OP_CHECKSIG), GenericTransactionSignatureChecker::CheckLockTime (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP65, BIP141, BIP147

import Definitions.Def_BitcoinHtlc
import Definitions.Def_BitcoinScript
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinHtlc.offered_timeout (f : Flags) (o : Oracle) (revHash remoteKey localKey payHash x localSig remoteSig dummy : Bytes)
    (hrev : revHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hrem : remoteKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hloc : localKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hb : o.hash160 x ≠ revHash) (h32 : x.length ≠ 32) :
    BitcoinScript.evalScript f o [x, localSig, remoteSig, dummy] (BitcoinHtlc.offeredScript revHash remoteKey localKey payHash) =
      match BitcoinScript.multisigLoop o [localSig, remoteSig] [localKey, remoteKey] with
      | none => none
      | some ok => if f.nulldummy && !dummy.isEmpty then none else some [BitcoinScript.boolBytes ok] := by sorry
