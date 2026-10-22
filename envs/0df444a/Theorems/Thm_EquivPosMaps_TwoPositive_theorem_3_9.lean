-- Prove2me | Theorems.Thm_EquivPosMaps_TwoPositive_theorem_3_9
-- name    : EquivPosMaps.TwoPositive.theorem_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:26:45.661855+00:00
-- url     : https://prove2.me/theorems/7c54ace7-5526-4fdc-9c1d-e049fa116eeb
-- title:
--   Theorem 3.9: 2-positive and not completely positive
-- statement:
--   For real $\alpha,\beta$, let $\Phi[\alpha,\beta]=\Phi_{\alpha,\beta,3}$. Define $\ell_P(\beta)=[-(2+3\beta)+\sqrt{9\beta^2-4\beta+4}]/2$, $\ell_{CP}(\beta)=[-(3+3\beta)+\sqrt{9\beta^2-10\beta+17}]/2$, and let $S_\beta$ be the least real root of $x^3+(-2-3\beta)x^2+(-2+4\beta)x+2\beta$. Then
--
--   $$
--   \Phi[\alpha,\beta]\text{ is 2-positive and not completely positive}
--   \quad\Longleftrightarrow\quad
--   \beta\leq-\tfrac15\;\text{ and }\;
--   \alpha\in[\ell_P(\beta),\ell_{CP}(\beta))\cap[1,\infty)\cap[-S_\beta,\infty).
--   $$
--
--   This is the paper's exact classification of the target parameter region. The square-root interval is closed on the left and open on the right.
-- source:
--   Collins, Osaka & Sapra, On a family of a linear maps from Mn(C) to Mn2(C), arXiv:1802.07553v1, p. 10, Theorem 3.9

import Mathlib
import Definitions.Def_EquivPosMaps_TwoPositive_Basic
open scoped Matrix Kronecker ComplexOrder
noncomputable section

namespace EquivPosMaps.TwoPositive
/-- Theorem 3.9, p. 10: exact 2-positive but not completely positive region. -/
theorem theorem_3_9 (α β : ℝ) :
    (KPositive 2 (phi 3 α β) ∧
      ¬ QAlgorithms.Entanglement.IsCompletelyPositive (phi 3 α β)) ↔
      (β ≤ -1/5 ∧ lowP 3 β ≤ α ∧ α < lowCP β ∧
        1 ≤ α ∧ -smallestRoot β ≤ α) := by sorry

end EquivPosMaps.TwoPositive
