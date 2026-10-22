-- Prove2me | Theorems.Thm_EquivPosMaps_TwoPositive_theorem_3_8
-- name    : EquivPosMaps.TwoPositive.theorem_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:27:03.553239+00:00
-- url     : https://prove2.me/theorems/50e60e02-f3ca-43f5-b31d-8fddbe7a0049
-- title:
--   Theorem 3.8: exact 2-positivity boundary
-- statement:
--   For real $\alpha,\beta$, let $S_\beta$ be the least real root of $x^3+(-2-3\beta)x^2+(-2+4\beta)x+2\beta$. Then
--
--   $$
--   \Phi[\alpha,\beta]\text{ is 2-positive}
--   \quad\Longleftrightarrow\quad
--   \alpha\in[1,\infty)\cap[-S_\beta,\infty).
--   $$
--
--   This determines the 2-positive region of the family and supplies the cubic-root boundary in the main result. Both lower endpoints are included.
-- source:
--   Collins, Osaka & Sapra, On a family of a linear maps from Mn(C) to Mn2(C), arXiv:1802.07553v1, p. 10, Theorem 3.8

import Mathlib
import Definitions.Def_EquivPosMaps_TwoPositive_Basic
open scoped Matrix Kronecker ComplexOrder
noncomputable section

namespace EquivPosMaps.TwoPositive
/-- Theorem 3.8, p. 10: exact 2-positivity threshold. -/
theorem theorem_3_8 (α β : ℝ) :
    KPositive 2 (phi 3 α β) ↔ (1 ≤ α ∧ -smallestRoot β ≤ α) := by sorry

end EquivPosMaps.TwoPositive
