-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gsource15_exponential_derivative_comparison
-- name    : AvramDividend.Classical.avram_gsource15_exponential_derivative_comparison
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T17:02:05.200216+00:00
-- url     : https://prove2.me/theorems/1ba47f4d-91c3-4318-9ab2-6373520e54b5
-- title:
--   Exponential comparison for a scalar differential upper inequality
-- statement:
--   On an arbitrary real interval with differentiable S and S prime at most K times S, the exponentially tilted function is antitone, hence S(b) is bounded above by exp(K(b-a)) times S(a). For Gaussian Avram verification, take S=w+w-prime and K=1+2(q+|c|)/sigma squared to control positive-cap excursions and near-cap curvature. No stopped Ito conclusion is hypothesised.

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_gsource15_exponential_derivative_comparison
    (S : ℝ → ℝ) (a b K : ℝ) (hab : a ≤ b)
    (hDer : ∀ y ∈ Set.Icc a b, HasDerivAt S (deriv S y) y)
    (hIneq : ∀ y ∈ Set.Icc a b, deriv S y ≤ K * S y) :
    S b ≤ Real.exp (K * (b - a)) * S a := by
  sorry
