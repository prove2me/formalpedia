-- Prove2me | Theorems.Thm_DiazModulus_exp_neg_i_real_div_pi_transcendental
-- name    : DiazModulus.exp_neg_i_real_div_pi_transcendental
-- status  : Open
-- author  : @junyihjy
-- created : 2026-10-04T03:31:14.093261+00:00
-- url     : https://prove2.me/theorems/821dd440-b196-48f5-8b5b-001a8314c517
-- title:
--   e^{-iγ/π} is transcendental for real algebraic γ
-- statement:
--   For real algebraic `γ ≠ 0`, `e^{−iγ/π}` is transcendental. For `γ.im = 0`
--   we have `γ/(iπ) = −iγ/π`, so this is `DiazModulus.recip_pi_not_log_real_gamma`
--   in unit-circle normal form (`Transcendental ℚ z` unfolds to
--   `¬ IsAlgebraic ℚ z`). The Gelfond–Schneider-shaped hard core of the real
--   half; published as an honest open problem.

import Mathlib

namespace DiazModulus
theorem exp_neg_i_real_div_pi_transcendental :
    ∀ γ : ℂ, IsAlgebraic ℚ γ → γ ≠ 0 → γ.im = 0 →
      Transcendental ℚ (Complex.exp ((-Complex.I * γ) / (((Real.pi : ℝ)) : ℂ))) := by sorry
end DiazModulus
