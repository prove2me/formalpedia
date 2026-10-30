-- Prove2me | Theorems.Thm_BitcoinHtlc_received_spends_iff
-- name    : BitcoinHtlc.received_spends_iff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T17:28:02.832601+00:00
-- url     : https://prove2.me/theorems/67b324ab-6401-4207-8d0e-dab655a929e4
-- title:
--   Received HTLC: the three spending conditions, for any witness stack
-- statement:
--   For pushed strings of at most 520 bytes, $|{\rm expiry}| < 2^{32}$ and any stack `st`: the witness-v0 success condition holds iff `ReceivedSpend f o … expiry st`.
-- source:
--   BOLT #3, Bitcoin Transaction and Script Formats, 'Offered HTLC Outputs' and 'Received HTLC Outputs': https://github.com/lightning/bolts/blob/master/03-transactions.md#offered-htlc-outputs; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_DUP, OP_HASH160, OP_EQUAL, OP_IF/OP_NOTIF, OP_SWAP, OP_SIZE, OP_CHECKMULTISIG, OP_CHECKLOCKTIMEVERIFY, OP_CHECKSIG), GenericTransactionSignatureChecker::CheckLockTime (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP65, BIP141, BIP147

import Definitions.Def_BitcoinHtlc
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinVerify
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinHtlc.received_spends_iff (f : Flags) (o : Oracle) (revHash remoteKey localKey payHash : Bytes) (expiry : Int)
    (st : List Bytes)
    (hrev : revHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hrem : remoteKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hloc : localKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hd : expiry.natAbs < 2 ^ 32) :
    (∃ res, BitcoinScript.evalScript f o st (BitcoinHtlc.receivedScript revHash remoteKey localKey payHash expiry) = some res ∧
        res.length = 1 ∧ BitcoinVerify.topTrue res = true) ↔
      BitcoinHtlc.ReceivedSpend f o revHash remoteKey localKey payHash expiry st := by sorry
