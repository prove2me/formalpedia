-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_random_pre_ruin_full_cash_source_budget
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_original_random_pre_ruin_full_cash_source_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:39:05.529513+00:00
-- url     : https://prove2.me/theorems/019e1c6e-6628-47c9-8d43-f3be0080b57f
-- title:
--   Original BV pre-ruin random-clock full Stieltjes cash and after-payment source budget
-- statement:
--   At an arbitrary original random time τ strictly before ruin on the realised path, the original full Stieltjes dividend cash, initial right-payment atom and post-right-payment reserve value are bounded by the original source-only cap-linear increment. No optional stopping theorem, new stochastic assumption, or fixed-clock approximation is used; the result is a pathwise localisation interface for P3-A and P3-B.
-- source:
--   Apply Proved original true-horizon full-cash source budget 72e66014-7076-428a-a5c9-785cea1ba7eb at the sample-dependent horizon τ ω. Both the original source and payment chronology remain definitionally unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p3_c_bvchain_original_random_pre_ruin_full_cash_source_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
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
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0) (ω : Ω)
    (hPre : (τ ω : ℝ≥0∞) < ruinTime X x D ω) :
    rightLimit D 0 ω +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (0 : ℝ) (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
      w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω) - w x ≤
      V (x + X.X (τ ω) ω - rightLimit D 0 ω) -
        V (x - rightLimit D 0 ω) := by sorry
