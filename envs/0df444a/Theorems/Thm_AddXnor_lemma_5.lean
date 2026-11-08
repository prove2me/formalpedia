-- Prove2me | Theorems.Thm_AddXnor_lemma_5
-- name    : AddXnor.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:57:40.026034+00:00
-- url     : https://prove2.me/theorems/4119460b-ecca-4357-85a2-0511b5f08fb5
-- title:
--   Lemma 5 (Four-bit guard) — only $++++$ and $\mathrm{XXXX}$ return $y$ to $1$
-- statement:
--   Consider the normalized updates (3) modulo $16$, starting from $(y, \varepsilon) = (1, 0)$, with operands $(3, 13, 3, 13)$ in that order and arbitrary operators $o_1, o_2, o_3, o_4 \in \{+, \odot\}$. Then
--
--   1. the final value of $y$ is $1$ if and only if all four operators are additions or all four are XNORs;
--   2. both of these patterns end with $\varepsilon = 0$.
--
--   This is the guard that forces each gadget of the reduction to be $++++$ or $\mathrm{XXXX}$ (Table 3 lists all sixteen patterns).
--
--   **Formalization Note** Words modulo 16 are `BitVec 4`; the operators are a function $o : \{0,1,2,3\} \to$ `Bool` (`true` = XNOR), and the run is `normRun` from `(1, false)`.
--
--   Differences from the source:
--   - encoding: operators $o_1, \dots, o_4$ → $o\,0, \dots, o\,3$ as Booleans; reason: same sixteen patterns
--   - encoding: arithmetic modulo $16$ → `BitVec 4`; reason: same residues
-- source:
--   Wang, Lv, Shen, Zhang, Add/XNOR Chains: An NP-Complete Boolean–Arithmetic Problem at the Meet-in-the-Middle Barrier, manuscript (sha256 405d6dda…), Lemma 5 and Table 3, p.9 (PDF p.9)

import Mathlib
import Definitions.Def_AddXnor_normStep

namespace AddXnor

/-- **Lemma 5 (Four-bit guard)** (Wang, Lv, Shen, Zhang, *Add/XNOR Chains*, manuscript, sha256 405d6dda…, Lemma 5, p.9 (PDF p.9)). Run the normalized updates
(3) modulo 16 (`m = 4`) from `(y, ε) = (1, 0)` on the operands `(3, 13, 3, 13)` in that order,
with operators `o 0, …, o 3` (`false` = `+`, `true` = XNOR). The final `y` is `1` iff all four
operators are additions or all four are XNORs; and both of these patterns end with `ε = 0`. -/
theorem lemma_5 (o : Fin 4 → Bool) :
    ((normRun ((1 : BitVec 4), false)
        (List.ofFn fun j : Fin 4 => (o j, (![3, 13, 3, 13] : Fin 4 → BitVec 4) j))).1 = 1 ↔
      (∀ j, o j = false) ∨ (∀ j, o j = true)) ∧
    ((∀ j, o j = false) ∨ (∀ j, o j = true) →
      (normRun ((1 : BitVec 4), false)
        (List.ofFn fun j : Fin 4 => (o j, (![3, 13, 3, 13] : Fin 4 → BitVec 4) j))).2 = false) := by sorry

end AddXnor
