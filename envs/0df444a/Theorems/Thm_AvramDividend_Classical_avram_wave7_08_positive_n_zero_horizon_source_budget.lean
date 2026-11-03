-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_08_positive_n_zero_horizon_source_budget
-- name    : AvramDividend.Classical.avram_wave7_08_positive_n_zero_horizon_source_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:56:47.641533+00:00
-- url     : https://prove2.me/theorems/89a2f273-164f-4f94-a266-2a3520a978db
-- title:
--   Positive n original stopped clock at T=0 is bounded by corrected initial-dividend estimate
-- statement:
--   For n>0, the true source stopped horizon min(ruinTime,n) retains at T=0 only original source time-zero payments, and the full expected Stieltjes cash is bounded by w(x) from the corrected zero-horizon theorem. This is the nonnegative horizon boundary case missing from the positive T stochastic core.
-- source:
--   Uses Proved db25d81e source paymentTimes inclusion and Proved 3858a86b corrected UBV zero-horizon bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_08_positive_n_zero_horizon_source_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
