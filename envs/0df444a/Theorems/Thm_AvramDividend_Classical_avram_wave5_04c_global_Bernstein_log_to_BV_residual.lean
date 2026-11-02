-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_global_Bernstein_log_to_BV_residual
-- name    : AvramDividend.Classical.avram_wave5_04c_global_Bernstein_log_to_BV_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:28:45.291254+00:00
-- url     : https://prove2.me/theorems/8ddb0ff7-052f-42c7-b438-223d273ed479
-- title:
--   Exponential compactification transfers weighted C1 polynomial error to physical BV residual
-- statement:
--   For nonnegative original BV residual r, substitution t=exp(-r) transforms the global endpoint-weighted Bernstein polynomial bound into ε(1-exp(-r)) plus 2L*r only when r>M. This is the exact form needed to integrate against the original source and use the proven normalized residual tail uniform-integrability theorem.
-- source:
--   Exponential-logarithmic inversion and order equivalence of cutoff predicates.

import Mathlib
set_option autoImplicit false
open Set

theorem AvramDividend.Classical.avram_wave5_04c_global_Bernstein_log_to_BV_residual (w : ℝ → ℝ) (Q : Polynomial ℝ)
    (x M ε L : ℝ) (hM : 0 ≤ M)
    (hQ : ∀ t : unitInterval.Elem, 0 < (t : ℝ) →
      |Polynomial.eval (t : ℝ) Q -
        (w x - w (x + Real.log (t : ℝ)))| ≤
        ε * (1 - (t : ℝ)) +
          (if (t : ℝ) < Real.exp (-M)
            then 2 * L * |Real.log (t : ℝ)| else 0)) :
    ∀ r : ℝ, 0 ≤ r →
      |Polynomial.eval (Real.exp (-r)) Q - (w x - w (x - r))| ≤
        ε * (1 - Real.exp (-r)) +
          (if M < r then 2 * L * r else 0) := by sorry
