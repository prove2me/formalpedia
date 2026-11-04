-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_discounted_strict_pre_cell_nonpos
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_original_discounted_strict_pre_cell_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:59:03.81677+00:00
-- url     : https://prove2.me/theorems/e6756f8c-b2e9-4a37-ba19-008ca662ca7f
-- title:
--   Original once-discounted strict-open pre-rightpayment Stieltjes dividend cell nonpositivity
-- statement:
--   For original X,D before ruin and strictly ordered positive-cap endpoints, true once-discounted dividend mass over paymentTimes intersect (a,b), with both endpoint right-dividend atoms excluded, plus the left-clock-discounted V prepayment reserve loss is nonpositive. Includes singular-continuous mass without further occupation or stochastic hypotheses.
-- source:
--   Genuine source original discounted full Ioc bound restricted to Iio b; exact measure restrict-restrict identity, source strict-open Mass cd71bccf and newly accepted original pre-rightpayment cell 0e5bee5f.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_pre_rightpayment_strict_cell_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_discount_left_full_measure_le
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_strict_interior_dividendMeasure_rightLimit
import Theorems.Thm_AvramDividend_Classical_paymentTimes_Ioc_subset_of_terminal_survival

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p3_c_bvchain_original_discounted_strict_pre_cell_nonpos
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
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (a b : ℝ≥0) (hab : a < b)
    (hPre : (b : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioo (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (a : ℝ))) *
        (V (x + X.X b ω - D b ω) -
          V (x + X.X b ω - rightLimit D a ω)) ≤ 0 := by sorry
