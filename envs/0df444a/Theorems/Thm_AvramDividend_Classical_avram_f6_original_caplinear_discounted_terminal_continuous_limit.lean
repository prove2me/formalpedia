-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_caplinear_discounted_terminal_continuous_limit
-- name    : AvramDividend.Classical.avram_f6_original_caplinear_discounted_terminal_continuous_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:26:24.996066+00:00
-- url     : https://prove2.me/theorems/21b68cac-dd3b-460a-957d-898d40103e81
-- title:
--   Original nonnegative caplinear discounted terminal converges at a right-delayed physical clock
-- statement:
--   For convergent original physical nonnegative clocks and eventually nonnegative convergent postpayment reserves, discounted exact all-cap caplinear HJB terminal reward converges to its value at the true clock. Uses only genuine original caplinear function continuity within nonnegative reserves.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_allcap_caplinear_continuousOn_nonnegative
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_caplinear_discounted_terminal_continuous_limit
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0)) (C : ℝ≥0∞)
    (q : ℝ) (a : ℕ → ℝ≥0) (s : ℝ≥0)
    (ha : Tendsto a atTop (𝓝 s))
    (Y : ℕ → ℝ) (y : ℝ)
    (hY : Tendsto Y atTop (𝓝 y)) (hy : 0 ≤ y)
    (hYpos : ∀ᶠ m : ℕ in atTop, 0 ≤ Y m) :
    Tendsto (fun m =>
      Real.exp (-(q * (a m : ℝ))) *
        (if ENNReal.ofReal (Y m) ≤ C then w (Y m)
         else w C.toReal + (Y m - C.toReal)))
      atTop (𝓝 (Real.exp (-(q * (s : ℝ))) *
        (if ENNReal.ofReal y ≤ C then w y
         else w C.toReal + (y - C.toReal)))) := by sorry
