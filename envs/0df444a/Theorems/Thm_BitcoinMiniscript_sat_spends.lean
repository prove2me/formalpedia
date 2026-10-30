-- Prove2me | Theorems.Thm_BitcoinMiniscript_sat_spends
-- name    : BitcoinMiniscript.sat_spends
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:25:32.491156+00:00
-- url     : https://prove2.me/theorems/326c38d8-474b-4e34-adad-84991b745a09
-- title:
--   A satisfaction spends: one true element is left
-- statement:
--   For `m : B` and `Sat f o m w` with bounds: `evalScript f o w (compile m)` leaves exactly one element, and it is true. This is the success condition of witness-v0 and tapscript execution.
-- source:
--   Miniscript reference (P. Wuille, A. Poelstra, S. Kanjalkar): translation table, type system and correctness/malleability properties, https://bitcoin.sipa.be/miniscript/; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: src/script/miniscript.h, src/script/miniscript.cpp (https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/miniscript.h); EvalScript (src/script/interpreter.cpp)

import Definitions.Def_BitcoinMiniscript
import Definitions.Def_BitcoinScript
open BitcoinMiniscript BitcoinToLocal BitcoinHtlc BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinMiniscript.sat_spends (f : BitcoinScript.Flags) (o : BitcoinScript.Oracle) (m : BitcoinMiniscript.Ms)
    (ht : BitcoinMiniscript.HasType m .B) (w : List BitcoinScript.Bytes) (hs : BitcoinMiniscript.Sat f o m w)
    (hops : BitcoinMiniscript.opsMax m ≤ BitcoinScript.MAX_OPS_PER_SCRIPT)
    (hsz : w.length + BitcoinMiniscript.size m ≤ BitcoinScript.MAX_STACK_SIZE) :
    ∃ res, BitcoinScript.evalScript f o w (BitcoinMiniscript.compile m) = some res ∧ res.length = 1 ∧
      (match res with | top :: _ => BitcoinScript.castToBool top | [] => false) = true := by sorry
