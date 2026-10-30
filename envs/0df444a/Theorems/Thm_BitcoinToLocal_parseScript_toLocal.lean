-- Prove2me | Theorems.Thm_BitcoinToLocal_parseScript_toLocal
-- name    : BitcoinToLocal.parseScript_toLocal
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T15:10:06.272293+00:00
-- url     : https://prove2.me/theorems/e9c457e8-9ec5-49c7-9a72-1706128fcf5c
-- title:
--   The byte form parses to the instruction form
-- statement:
--   For keys of at most 520 bytes and $|{\rm delay}| < 2^{32}$: `parseScript (toLocalBytes rev delay dpk) = some (toLocalScript rev delay dpk)`, through `GetOp` on the canonical pushes and `CScript`'s small-integer encoding.
-- source:
--   BOLT #3, Bitcoin Transaction and Script Formats, 'to_local Output': https://github.com/lightning/bolts/blob/master/03-transactions.md#to_local-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_IF/OP_ELSE/OP_ENDIF, OP_CHECKSEQUENCEVERIFY, OP_CHECKSIG), GenericTransactionSignatureChecker::CheckSequence, ExecuteWitnessScript, VerifyWitnessProgram (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); CScript::operator<<(int64_t) (script/script.h); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinToLocal
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSig
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinToLocal.parseScript_toLocal (rev dpk : Bytes) (delay : Int)
    (hrev : rev.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hdpk : dpk.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hd : delay.natAbs < 2 ^ 32) :
    BitcoinSig.parseScript (BitcoinToLocal.toLocalBytes rev delay dpk) = some (BitcoinToLocal.toLocalScript rev delay dpk) := by sorry
