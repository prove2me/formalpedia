-- Prove2me | Theorems.Thm_EquivPosMaps_TwoPositive_theorem_3_6
-- name    : EquivPosMaps.TwoPositive.theorem_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:26:46.79535+00:00
-- url     : https://prove2.me/theorems/277d1414-ce39-42fb-bd36-51b50c64cee0
-- title:
--   Theorem 3.6: positive but not completely positive region
-- statement:
--   For $\Phi[\alpha,\beta]=\Phi_{\alpha,\beta,3}$, write $\ell_P(\beta)=\ell_P(3,\beta)$ and let $\ell_{CP}(\beta)$ be the complete positivity boundary. The map is positive but not completely positive exactly when the applicable case holds:
--
--   $$
--   \begin{aligned}
--   \beta\leq-\tfrac15 &: \quad \ell_P(\beta)\leq\alpha<\ell_{CP}(\beta),\\
--   -\tfrac15\leq\beta\leq0 &: \quad \ell_P(\beta)\leq\alpha<1,\\
--   \beta\geq0 &: \quad 0\leq\alpha<1.
--   \end{aligned}
--   $$
--
--   The left endpoints are included and the right endpoints excluded. The conditions overlap at two boundary values of $\beta$ and agree there. This criterion is one of the paper's two direct inputs to Theorem 3.9.
-- source:
--   Collins, Osaka & Sapra, On a family of a linear maps from Mn(C) to Mn2(C), arXiv:1802.07553v1, p. 9, Theorem 3.6

import Mathlib
import Definitions.Def_EquivPosMaps_TwoPositive_Basic
open scoped Matrix Kronecker ComplexOrder
noncomputable section

namespace EquivPosMaps.TwoPositive
/-- Theorem 3.6, p. 9: the positive but not completely positive region. -/
theorem theorem_3_6 (α β : ℝ) :
    (IsPositiveMap (phi 3 α β) ∧
      ¬ QAlgorithms.Entanglement.IsCompletelyPositive (phi 3 α β)) ↔
      ((β ≤ -1/5 → lowP 3 β ≤ α ∧ α < lowCP β) ∧
        (-1/5 ≤ β ∧ β ≤ 0 → lowP 3 β ≤ α ∧ α < 1) ∧
        (0 ≤ β → 0 ≤ α ∧ α < 1)) := by sorry

end EquivPosMaps.TwoPositive
