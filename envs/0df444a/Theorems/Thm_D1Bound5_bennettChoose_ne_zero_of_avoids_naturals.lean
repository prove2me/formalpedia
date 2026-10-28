-- Prove2me | Theorems.Thm_D1Bound5_bennettChoose_ne_zero_of_avoids_naturals
-- name    : D1Bound5.bennettChoose_ne_zero_of_avoids_naturals
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:29:09.536108+00:00
-- url     : https://prove2.me/theorems/5d588da6-158a-40bf-8859-0bcc4aff8a1e
-- title:
--   Bennett Choose ne zero of avoids naturals
-- statement:
--   A generalized binomial coefficient is nonzero whenever its upper parameter avoids the first k natural numbers.
-- source:
--   D1Bound5/BennettChooseNonzero.lean, lines 11-26, SHA-256 242284e834a07d1f10f92c6ff0dc397a65048f9ca805d58c05766b00a9bc4ab5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.LinearCombination

section
open Polynomial

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]


theorem _root_.D1Bound5.bennettChoose_ne_zero_of_avoids_naturals (r : F) (k : ℕ)
    (h : ∀ j : ℕ, j < k → r ≠ (j : F)) : Ring.choose r k ≠ 0 := by sorry





end D1Bound5
end
