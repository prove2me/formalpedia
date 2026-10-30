-- Prove2me | Theorems.Thm_BitcoinToLocal_serialize_length
-- name    : BitcoinToLocal.serialize_length
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T15:09:24.764058+00:00
-- url     : https://prove2.me/theorems/e2a35841-31ca-4155-b7ab-c843ab0d0fef
-- title:
--   A script number below 2^(8k) in magnitude serializes to at most k + 1 bytes
-- statement:
--   For an integer $n$ and $k$ with $|n| < 256^k$: `(serialize n).length ≤ k + 1`. In particular a delay below $2^{32}$ fits the 5-byte limit of `OP_CHECKSEQUENCEVERIFY`.
-- source:
--   BOLT #3, Bitcoin Transaction and Script Formats, 'to_local Output': https://github.com/lightning/bolts/blob/master/03-transactions.md#to_local-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_IF/OP_ELSE/OP_ENDIF, OP_CHECKSEQUENCEVERIFY, OP_CHECKSIG), GenericTransactionSignatureChecker::CheckSequence, ExecuteWitnessScript, VerifyWitnessProgram (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); CScript::operator<<(int64_t) (script/script.h); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinToLocal
import Definitions.Def_BitcoinScript
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinToLocal.serialize_length (n : Int) (k : Nat) (h : n.natAbs < 256 ^ k) :
    (BitcoinScript.serialize n).length ≤ k + 1 := by sorry
