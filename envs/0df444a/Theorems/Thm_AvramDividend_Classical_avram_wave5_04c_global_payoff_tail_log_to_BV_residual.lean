-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_global_payoff_tail_log_to_BV_residual
-- name    : AvramDividend.Classical.avram_wave5_04c_global_payoff_tail_log_to_BV_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:43:31.273203+00:00
-- url     : https://prove2.me/theorems/f37db009-7b9c-483f-a4ed-caf8ca33c7b2
-- title:
--   Sharp exponential compactification preserving signed-payoff integrable far negative jump tails
-- statement:
--   Transports the sharp endpoint-weighted polynomial approximation under t=exp(-r), preserving the actual signed payoff increment rather than degrading it to a global first-moment |r| bound. This is valid simultaneously for integration against the true BV negative Lévy measure (using GeneratorIntegrable) and for original-source expected residual tails (using Lipschitz and first moment).
-- source:
--   Exact logarithm-exponential inversion, monotonic cutoff equivalence, and payoff residual substitution.

import Mathlib
set_option autoImplicit false
open Set

theorem AvramDividend.Classical.avram_wave5_04c_global_payoff_tail_log_to_BV_residual (w : ℝ → ℝ) (Q : Polynomial ℝ)
    (x M ε : ℝ) (hM : 0 ≤ M)
    (hQ : ∀ t : unitInterval.Elem, 0 < (t : ℝ) →
      |Polynomial.eval (t : ℝ) Q -
        (w x - w (x + Real.log (t : ℝ)))| ≤
        ε * (1 - (t : ℝ)) +
          (if (t : ℝ) < Real.exp (-M)
            then 2 * |w x - w (x + Real.log (t : ℝ))| else 0)) :
    ∀ r : ℝ, 0 ≤ r →
      |Polynomial.eval (Real.exp (-r)) Q - (w x - w (x - r))| ≤
        ε * (1 - Real.exp (-r)) +
          (if M < r then 2 * |w x - w (x - r)| else 0) := by sorry
