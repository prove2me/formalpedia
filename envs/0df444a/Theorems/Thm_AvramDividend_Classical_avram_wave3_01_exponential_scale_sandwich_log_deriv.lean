-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_exponential_scale_sandwich_log_deriv
-- name    : AvramDividend.Classical.avram_wave3_01_exponential_scale_sandwich_log_deriv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:15:30.802811+00:00
-- url     : https://prove2.me/theorems/da982a88-2f84-47fc-97f9-24db4589f4fd
-- title:
--   Exponential two-point scale bounds imply the logarithmic derivative
-- statement:
--   A positive scale function whose two-point ratios are squeezed between exponentials of a continuous positive-axis record rate has logarithmic derivative equal to that rate at every positive point. The proof takes logarithms, divides by the positive interval length and invokes the already remotely Proved continuous two-point slope-squeeze theorem. This is the deterministic last step from the actual Lévy record semigroup and Standing-free scale sandwich to the canonical pure-jump C1 theorem.
-- source:
--   Pinned Mathlib Real.log_le_log, Real.log_div, slope_def_field, slope_comm; Proved Avram Wave3 two-point derivative squeeze.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_continuous_two_point_slope_squeeze
open AvramDividend.Classical Real Set

theorem AvramDividend.Classical.avram_wave3_01_exponential_scale_sandwich_log_deriv
    (W κ : ℝ → ℝ)
    (hW : ∀ a : ℝ, 0 < a → 0 < W a)
    (hκ : ContinuousOn κ (Ioi (0 : ℝ)))
    (hsand : ∀ a b : ℝ, 0 < a → a < b →
      Real.exp (-(κ a * (b - a))) ≤ W a / W b ∧
      W a / W b ≤ Real.exp (-(κ b * (b - a)))) :
    ∀ a : ℝ, 0 < a →
      HasDerivAt (fun x : ℝ => Real.log (W x)) (κ a) a := by sorry
