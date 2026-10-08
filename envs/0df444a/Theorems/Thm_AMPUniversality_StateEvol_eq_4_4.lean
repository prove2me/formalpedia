-- Prove2me | Theorems.Thm_AMPUniversality_StateEvol_eq_4_4
-- name    : AMPUniversality.StateEvol.eq_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:33:42.765165+00:00
-- url     : https://prove2.me/theorems/bfbf922e-5f50-4ea3-9145-8a99e9ef9a3a
-- title:
--   Equation (4.4) — diagonal two-time covariance has four identical blocks
-- statement:
--   In a converging AMP sequence, the covariance of a joint state-evolution pair at equal positive times is concentrated on the diagonal:
--
--   $$\Sigma_a^{t,t}=\begin{pmatrix}\Sigma_a^t&\Sigma_a^t\\\Sigma_a^t&\Sigma_a^t\end{pmatrix},\qquad t\ge1.$$
--
--   This identifies one-time state evolution as the diagonal case of the two-time recursion. The statement also asserts positive semidefiniteness of the joint covariance, guarding the Gaussian construction.
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, p. 15, (4.4)

import Definitions.Def_AMPUniversality_StateEvol_SETwo

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace AMPUniversality.StateEvol

/-- Equation (4.4): the two-time covariance on the diagonal has four equal blocks. -/
theorem eq_4_4 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {q h k d : ℕ}
    (M : Model Ω q h k d) (hconv : IsConverging P M)
    (t : ℕ) (ht : 1 ≤ t) (a : Fin k) :
    (M.seTwo t t a).PosSemidef ∧
    M.seTwo t t a = Matrix.fromBlocks (M.se t a) (M.se t a)
      (M.se t a) (M.se t a) := by sorry

end AMPUniversality.StateEvol
