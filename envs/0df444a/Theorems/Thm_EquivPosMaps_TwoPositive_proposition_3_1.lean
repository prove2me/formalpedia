-- Prove2me | Theorems.Thm_EquivPosMaps_TwoPositive_proposition_3_1
-- name    : EquivPosMaps.TwoPositive.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:26:51.801845+00:00
-- url     : https://prove2.me/theorems/9d43d1f8-1310-4961-97e7-85010b950501
-- title:
--   Proposition 3.1: positivity of Φ at every n ≥ 3
-- statement:
--   For real $\alpha,\beta$ and an integer $n\geq3$, let $\Phi_{\alpha,\beta,n}$ be the paper's map and set $\ell_P(n,\beta)=[-(2+n\beta)+\sqrt{n^2\beta^2-4(n-2)\beta+4}]/2$. Then $\Phi_{\alpha,\beta,n}$ is positive exactly under the applicable conditions
--
--   $$
--   \beta\geq0\Longrightarrow\alpha\geq0,\qquad
--   \beta\leq0\Longrightarrow\alpha\geq\ell_P(n,\beta).
--   $$
--
--   The inequalities include their lower endpoints. This result identifies the positive region before the paper specializes to dimension three.
-- source:
--   Collins, Osaka & Sapra, On a family of a linear maps from Mn(C) to Mn2(C), arXiv:1802.07553v1, p. 6, Proposition 3.1

import Mathlib
import Definitions.Def_EquivPosMaps_TwoPositive_Basic
open scoped Matrix Kronecker ComplexOrder
noncomputable section

namespace EquivPosMaps.TwoPositive
/-- Proposition 3.1, p. 6: positivity of the general n family. -/
theorem proposition_3_1 (n : ℕ) (hn : 3 ≤ n) (α β : ℝ) :
    IsPositiveMap (phi n α β) ↔
      ((0 ≤ β → 0 ≤ α) ∧ (β ≤ 0 → lowP n β ≤ α)) := by sorry

end EquivPosMaps.TwoPositive
