-- Prove2me | Theorems.Thm_BitcoinHtlc_offered_revocation
-- name    : BitcoinHtlc.offered_revocation
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T17:26:32.555084+00:00
-- url     : https://prove2.me/theorems/ef3c822d-3a5c-4e37-8dc8-7120c99d9e67
-- title:
--   Offered HTLC, revocation path
-- statement:
--   For pushed strings of at most 520 bytes and `hash160 pk = revHash`: `evalScript f o [pk, sig] (offeredScript …) = (o.checkSig sig pk).map (fun ok => [boolBytes ok])`.
-- source:
--   BOLT #3, Bitcoin Transaction and Script Formats, 'Offered HTLC Outputs' and 'Received HTLC Outputs': https://github.com/lightning/bolts/blob/master/03-transactions.md#offered-htlc-outputs; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_DUP, OP_HASH160, OP_EQUAL, OP_IF/OP_NOTIF, OP_SWAP, OP_SIZE, OP_CHECKMULTISIG, OP_CHECKLOCKTIMEVERIFY, OP_CHECKSIG), GenericTransactionSignatureChecker::CheckLockTime (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP65, BIP141, BIP147

import Definitions.Def_BitcoinHtlc
import Definitions.Def_BitcoinScript
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinHtlc.offered_revocation (f : Flags) (o : Oracle) (revHash remoteKey localKey payHash pk sig : Bytes)
    (hrev : revHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hrem : remoteKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hloc : localKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hb : o.hash160 pk = revHash) :
    BitcoinScript.evalScript f o [pk, sig] (BitcoinHtlc.offeredScript revHash remoteKey localKey payHash) =
      (o.checkSig sig pk).map (fun ok => [BitcoinScript.boolBytes ok]) := by sorry
