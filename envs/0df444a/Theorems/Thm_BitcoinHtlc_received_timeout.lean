-- Prove2me | Theorems.Thm_BitcoinHtlc_received_timeout
-- name    : BitcoinHtlc.received_timeout
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T17:27:49.809678+00:00
-- url     : https://prove2.me/theorems/0e833a91-d47c-49c4-8fea-44b80d21aae3
-- title:
--   Received HTLC, timeout path (CLTV)
-- statement:
--   For pushed strings of at most 520 bytes, `hash160 x ≠ revHash` and `x` not 32 bytes: on `[x, sig]` the script fails unless `CltvPasses f o expiry`, then leaves the remote-key signature check.
-- source:
--   BOLT #3, Bitcoin Transaction and Script Formats, 'Offered HTLC Outputs' and 'Received HTLC Outputs': https://github.com/lightning/bolts/blob/master/03-transactions.md#offered-htlc-outputs; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_DUP, OP_HASH160, OP_EQUAL, OP_IF/OP_NOTIF, OP_SWAP, OP_SIZE, OP_CHECKMULTISIG, OP_CHECKLOCKTIMEVERIFY, OP_CHECKSIG), GenericTransactionSignatureChecker::CheckLockTime (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP65, BIP141, BIP147

import Definitions.Def_BitcoinHtlc
import Definitions.Def_BitcoinScript
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinHtlc.received_timeout (f : Flags) (o : Oracle) (revHash remoteKey localKey payHash x sig : Bytes) (expiry : Int)
    (hrev : revHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hrem : remoteKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hloc : localKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hd : expiry.natAbs < 2 ^ 32) (hb : o.hash160 x ≠ revHash) (h32 : x.length ≠ 32) :
    BitcoinScript.evalScript f o [x, sig] (BitcoinHtlc.receivedScript revHash remoteKey localKey payHash expiry) =
      if BitcoinHtlc.CltvPasses f o expiry then (o.checkSig sig remoteKey).map (fun ok => [BitcoinScript.boolBytes ok]) else none := by sorry
