-- Prove2me | Theorems.Thm_BitcoinMiniscript_compile_skip
-- name    : BitcoinMiniscript.compile_skip
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:23:29.156711+00:00
-- url     : https://prove2.me/theorems/dcaae477-a335-4c5c-b776-482fc1a69e3d
-- title:
--   A typed fragment in a non-executing branch is skipped
-- statement:
--   For a well-typed fragment and a state whose condition stack is not all true, with room for its operations: `runSeq` over `compile m` leaves the stacks and condition stack unchanged and adds at most `opsMax m` to the operation count.
-- source:
--   Miniscript reference (P. Wuille, A. Poelstra, S. Kanjalkar): translation table, type system and correctness/malleability properties, https://bitcoin.sipa.be/miniscript/; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: src/script/miniscript.h, src/script/miniscript.cpp (https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/miniscript.h); EvalScript (src/script/interpreter.cpp)

import Definitions.Def_BitcoinMiniscript
import Definitions.Def_BitcoinScript
open BitcoinMiniscript BitcoinToLocal BitcoinHtlc BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinMiniscript.compile_skip (f : BitcoinScript.Flags) (o : BitcoinScript.Oracle) (m : BitcoinMiniscript.Ms)
    (ty : BitcoinMiniscript.Ty) (ht : BitcoinMiniscript.HasType m ty) (st alt : List BitcoinScript.Bytes)
    (vf : List Bool) (k : Nat) (hvf : BitcoinScript.allTrue vf = false)
    (hk : k + BitcoinMiniscript.opsMax m ≤ BitcoinScript.MAX_OPS_PER_SCRIPT)
    (hsz : st.length + alt.length ≤ BitcoinScript.MAX_STACK_SIZE) :
    ∃ k', BitcoinMiniscript.runSeq f o ⟨st, alt, vf, k⟩ (BitcoinMiniscript.compile m) = some ⟨st, alt, vf, k'⟩ ∧
      k' ≤ k + BitcoinMiniscript.opsMax m := by sorry
