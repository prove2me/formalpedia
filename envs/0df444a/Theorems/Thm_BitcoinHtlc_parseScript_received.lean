-- Prove2me | Theorems.Thm_BitcoinHtlc_parseScript_received
-- name    : BitcoinHtlc.parseScript_received
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T17:28:33.346511+00:00
-- url     : https://prove2.me/theorems/72a9677c-3e20-47ed-8191-963f25903574
-- title:
--   The received script's byte form parses to its instruction form
-- statement:
--   For pushed strings of at most 520 bytes and $|{\rm expiry}| < 2^{32}$: `parseScript (receivedBytes …) = some (receivedScript …)`.
-- source:
--   BOLT #3, Bitcoin Transaction and Script Formats, 'Offered HTLC Outputs' and 'Received HTLC Outputs': https://github.com/lightning/bolts/blob/master/03-transactions.md#offered-htlc-outputs; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_DUP, OP_HASH160, OP_EQUAL, OP_IF/OP_NOTIF, OP_SWAP, OP_SIZE, OP_CHECKMULTISIG, OP_CHECKLOCKTIMEVERIFY, OP_CHECKSIG), GenericTransactionSignatureChecker::CheckLockTime (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP65, BIP141, BIP147

import Definitions.Def_BitcoinHtlc
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSig
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinHtlc.parseScript_received (revHash remoteKey localKey payHash : Bytes) (expiry : Int)
    (hrev : revHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hrem : remoteKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hloc : localKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hd : expiry.natAbs < 2 ^ 32) :
    BitcoinSig.parseScript (BitcoinHtlc.receivedBytes revHash remoteKey localKey payHash expiry) =
      some (BitcoinHtlc.receivedScript revHash remoteKey localKey payHash expiry) := by sorry
