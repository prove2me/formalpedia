-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_08_all_n_zero_horizon_bounded_clock_budget
-- name    : AvramDividend.Classical.avram_wave7_08_all_n_zero_horizon_bounded_clock_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T13:06:24.404362+00:00
-- url     : https://prove2.me/theorems/a4ec4831-8af1-49f2-b115-bdf9a26b27b4
-- title:
--   All source bounded ruin clocks have the exact initial Stieltjes dividend budget at zero horizon
-- statement:
--   For every natural bounded ruin clock n and the original spectrally negative Lévy source process, the complete discounted Stieltjes cash up to time T=0 equals the initial right dividend atom, and is bounded by w(x) under the repaired boundary and jump hypotheses. The proof preserves the original paymentTimes(min(ruinTime,n)) convention and no probabilistic substitution is made.
-- source:
--   Zero-horizon-for-all-n boundary of corrected original bounded-clock budget 3c9532b7-1071-4d95-b7a6-9279a240132f, generalising the Proved original time-zero horizon theorem 3858a86b-eff8-46f1-b700-7ee855dad85a. This removes the T=0 boundary before the positive-clock positive-horizon original Ito-Meyer obligation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_08_all_n_zero_horizon_bounded_clock_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (n : ℕ) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
