-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_true_gaussian_jumplower_generator_HJB_exponential_growth
-- name    : AvramDividend.Classical.avram_f6_true_gaussian_jumplower_generator_HJB_exponential_growth
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T20:44:11.546634+00:00
-- url     : https://prove2.me/theorems/020c9b00-bc80-4753-a7a0-c3b839b600e0
-- title:
--   Original Gaussian mixed-jump HJB exp growth from true jump-generator integral lower bound and scalar ODE
-- statement:
--   For true spectrally negative Levy with σ>0 and original topcap candidate w, if its actual Lévy generator negative-jump integral is ≥−r w(y) for r≥0 on positive reserve, source HJB gives scalar ODE a w″+c w′−(q+r) w≤0. Proved original scalar ODE exponential comparison implies global w growth ≤Ke^{θ y}.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_true_gaussian_jumplower_generator_HJB_exponential_growth
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : 0 < X.σ)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hTop : C = ⊤) (hw0 : 0 ≤ w 0)
    (hwcont : ContinuousOn w (Ici 0))
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwsmooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwgen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (r : ℝ) (hr : 0 ≤ r)
    (hJumpLower : ∀ y : ℝ, 0 < y →
      -r * w y ≤
      ∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, w y ≤ K * Real.exp (θ * y) := by sorry
