-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_pre_rightpayment_strict_cell_nonpos
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_original_pre_rightpayment_strict_cell_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:51:42.834346+00:00
-- url     : https://prove2.me/theorems/0e5bee5f-4746-41a2-b2a5-7ebc22c8801b
-- title:
--   Original BV strict-open dividend source-frozen nonpositive cell ending before the right-horizon payment
-- statement:
--   For actual original source X and left-continuous admissible D, every strict pre-ruin a<b has the full continuous and interior right-atomic Stieltjes mass over (a,b) compensated by the loss in cap-linear V from post-payment state at a to pre-payment state at b. The right-horizon payment is excluded.
-- source:
--   Proved original strict-open dividend measure identity cd71bccf, monotone rightLim_le_leftLim, original dividend strategy left continuity, admissibility, and positive-cap global secant.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_real_extension_leftContinuous
import Theorems.Thm_AvramDividend_Classical_dividendPath_real_rightLim_eq_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_strict_interior_dividendMeasure_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p3_c_bvchain_original_pre_rightpayment_strict_cell_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (a b : ℝ≥0) (hab : a < b)
    (hPre : (b : ℝ≥0∞) < ruinTime X x D ω) :
    (dividendMeasure D ω (Ioo (a : ℝ) (b : ℝ))).toReal +
      V (x + X.X b ω - D b ω) -
      V (x + X.X b ω - rightLimit D a ω) ≤ 0 := by sorry
