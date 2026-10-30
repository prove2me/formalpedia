-- Prove2me | Theorems.Thm_BitcoinToLocal_spends_iff
-- name    : BitcoinToLocal.spends_iff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T15:09:53.847694+00:00
-- url     : https://prove2.me/theorems/011dc115-ffee-4831-82ca-73f075034a2d
-- title:
--   The two spending conditions, for any witness stack
-- statement:
--   For keys of at most 520 bytes and $|{\rm delay}| < 2^{32}$, and any stack `st`: there is a result of `evalScript f o st (toLocalScript rev delay dpk)` with exactly one element that is true, if and only if `st = [b, sig]` for some $b$, `sig` with `SpendCondition f o rev delay dpk b sig`. Stacks of any other shape fail: empty, one element, more than two (the extra elements remain below the result), or beyond the 1000-element limit.
-- source:
--   BOLT #3, Bitcoin Transaction and Script Formats, 'to_local Output': https://github.com/lightning/bolts/blob/master/03-transactions.md#to_local-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_IF/OP_ELSE/OP_ENDIF, OP_CHECKSEQUENCEVERIFY, OP_CHECKSIG), GenericTransactionSignatureChecker::CheckSequence, ExecuteWitnessScript, VerifyWitnessProgram (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); CScript::operator<<(int64_t) (script/script.h); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinToLocal
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinVerify
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinToLocal.spends_iff (f : Flags) (o : Oracle) (rev dpk : Bytes) (delay : Int) (st : List Bytes)
    (hrev : rev.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hdpk : dpk.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hd : delay.natAbs < 2 ^ 32) :
    (∃ res, BitcoinScript.evalScript f o st (BitcoinToLocal.toLocalScript rev delay dpk) = some res ∧
        res.length = 1 ∧ BitcoinVerify.topTrue res = true) ↔
      ∃ b sig, st = [b, sig] ∧ BitcoinToLocal.SpendCondition f o rev delay dpk b sig := by sorry
