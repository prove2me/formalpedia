-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb39_fourth_lintegral_bound_gives_real_integral
-- name    : AvramDividend.Classical.avram_gb39_fourth_lintegral_bound_gives_real_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:24:03.566304+00:00
-- url     : https://prove2.me/theorems/a5fb539e-0ab4-4025-a071-adb1737cb378
-- title:
--   Real fourth-moment integrability and mean bound from a finite ENNReal lintegral
-- statement:
--   A measurable real random variable with a fourth-moment ENNReal lintegral bounded by a finite nonnegative real B has an integrable real fourth power and its real expected fourth power is ≤B.
-- source:
--   Reusable elementary conversion of the Proved original Gaussian finite-grid fourth-moment lintegral estimate into the real integrability needed by gb34 and the bounded quadratic coefficient inequality gb38.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gb39_fourth_lintegral_bound_gives_real_integral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : Ω → ℝ) (hZ : Measurable Z) (B : ℝ) (hB : 0 ≤ B)
    (hFourth : (∫⁻ ω, ENNReal.ofReal (Z ω ^ 4) ∂P) ≤ ENNReal.ofReal B) :
    Integrable (fun ω => Z ω ^ 4) P ∧
      (∫ ω, Z ω ^ 4 ∂P) ≤ B := by sorry
