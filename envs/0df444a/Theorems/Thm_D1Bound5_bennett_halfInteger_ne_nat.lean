-- Prove2me | Theorems.Thm_D1Bound5_bennett_halfInteger_ne_nat
-- name    : D1Bound5.bennett_halfInteger_ne_nat
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:28:45.525801+00:00
-- url     : https://prove2.me/theorems/bd3ee6fc-dc14-4fb2-bc69-578b126a60dc
-- title:
--   Bennett half Integer ne nat
-- statement:
--   Every half-integer parameter in the Bennett node-removal induction differs from every natural number. This is the exact parity obstruction, transported through the characteristic-zero cast.
-- source:
--   D1Bound5/BennettChooseNonzero.lean, lines 28-38, SHA-256 242284e834a07d1f10f92c6ff0dc397a65048f9ca805d58c05766b00a9bc4ab5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.LinearCombination

section
open Polynomial

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]




theorem _root_.D1Bound5.bennett_halfInteger_ne_nat (k v j : ℕ) :
    (k : F) + (1 / 2 : F) - (v : F) * (k : F) ≠ (j : F) := by sorry



end D1Bound5
end
