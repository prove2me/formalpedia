-- Prove2me | Theorems.Thm_BitcoinMiniscript_sem_sound
-- name    : BitcoinMiniscript.sem_sound
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:24:29.948564+00:00
-- url     : https://prove2.me/theorems/f4a26477-40c8-40d6-8696-cec1abe3d792
-- title:
--   Compiler soundness for B, V and K: the script leaves exactly the semantic output
-- statement:
--   For a well-typed `m` of type other than `W`, with operation and stack bounds: `Sem f o m w out` implies `evalScript f o (w ++ rest) (compile m) = some (out ++ rest)`. The stack below the witness is untouched.
-- source:
--   Miniscript reference (P. Wuille, A. Poelstra, S. Kanjalkar): translation table, type system and correctness/malleability properties, https://bitcoin.sipa.be/miniscript/; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: src/script/miniscript.h, src/script/miniscript.cpp (https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/miniscript.h); EvalScript (src/script/interpreter.cpp)

import Definitions.Def_BitcoinMiniscript
import Definitions.Def_BitcoinScript
open BitcoinMiniscript BitcoinToLocal BitcoinHtlc BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinMiniscript.sem_sound (f : BitcoinScript.Flags) (o : BitcoinScript.Oracle) (m : BitcoinMiniscript.Ms)
    (ty : BitcoinMiniscript.Ty) (ht : BitcoinMiniscript.HasType m ty) (hne : ty ≠ .W)
    (w out rest : List BitcoinScript.Bytes) (hs : BitcoinMiniscript.Sem f o m w out)
    (hops : BitcoinMiniscript.opsMax m ≤ BitcoinScript.MAX_OPS_PER_SCRIPT)
    (hsz : w.length + rest.length + BitcoinMiniscript.size m ≤ BitcoinScript.MAX_STACK_SIZE) :
    BitcoinScript.evalScript f o (w ++ rest) (BitcoinMiniscript.compile m) = some (out ++ rest) := by sorry
