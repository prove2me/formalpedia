-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_clean_strict_horizon_frozen_source_grid_budget
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_original_clean_strict_horizon_frozen_source_grid_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:36:19.18506+00:00
-- url     : https://prove2.me/theorems/8a24eb9f-6159-4288-bd4f-da673d2b3f59
-- title:
--   Original controlled C1 BV strict-horizon finite-grid budget without nonpositive discount corrections
-- statement:
--   In the original admissible spectrally negative Levy controlled reserve with positive cap, C1 interior candidate, original w(0)≥0 and negative extension, gradient at least one, and genuine right-payment secants, the exact once-discounted time-zero plus full-grid plus strict-open final dividend payments and prepayment terminal candidate are dominated solely by frozen original-source increments. All nonpositive discount-clock terms are discharged using the source original post-payment and prepayment nonnegativity lemmas. No process-level stochastic compensation or assumed HJB conclusion is used.
-- source:
--   Original full-grid and strict-final BV discount identity 02e2ddd8, source candidate nonnegativity 5c1ea3f2/151fa4ac, elementary clock sign helper; Avram Proposition 4(i), Equation (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_hybrid_strict_horizon_discounted_grid_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_discount_stieltjes_clock_correction_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_bv_caplinear_postpayment_candidate_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave7_09_corrected_positive_cap_bv_postpayment_value_nonnegative_automatic
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_c_bvchain_original_clean_strict_horizon_frozen_source_grid_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x)
    (C : ℝ≥0∞) (hC : 0 < C) (hxc : ENNReal.ofReal x ≤ C)
    (w V : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
      w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ≥0) (n : ℕ) (hzero : u 0 = 0)
    (hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (hPre : ∀ i : ℕ, i < n → (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω)
    (b : ℝ≥0) (hFinal : u n < b)
    (hBPre : (b : ℝ≥0∞) < ruinTime X x D ω) :
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    let cash : ℕ → ℝ := fun i => (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
      Ioc (u i : ℝ) (u (i + 1) : ℝ), ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    let source : ℕ → ℝ := fun i => V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
      V (x + X.X (u i) ω - rightLimit D (u i) ω)
    let finalCash : ℝ := (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
      Ioo (u n : ℝ) (b : ℝ), ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    rightLimit D 0 ω + (∑ i ∈ Finset.range n, cash i) + finalCash +
      Real.exp (-(q * (b : ℝ))) * w (riskProcess X x D b ω) ≤
      w x + (∑ i ∈ Finset.range n, e i * source i) +
      e n * (V (x + X.X b ω - rightLimit D (u n) ω) -
        V (x + X.X (u n) ω - rightLimit D (u n) ω)) := by sorry
