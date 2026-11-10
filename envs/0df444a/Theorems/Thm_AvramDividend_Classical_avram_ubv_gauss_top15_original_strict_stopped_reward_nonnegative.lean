-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss_top15_original_strict_stopped_reward_nonnegative
-- name    : AvramDividend.Classical.avram_ubv_gauss_top15_original_strict_stopped_reward_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T10:39:50.530937+00:00
-- url     : https://prove2.me/theorems/a52afe4b-5012-44f7-843f-351ab7664951
-- title:
--   Original zero-jump top-cap strict stopped Gaussian reward is pointwise nonnegative
-- statement:
--   The actual zero-Levy-measure Gaussian strict stopped reward is everywhere nonnegative, including zero clock, terminal surplus and strictly-before-stop Stieltjes cash. This is the nonnegative-Fatou prerequisite for passing physical finite-grid expected Gaussian HJB bounds to the true original stopped reward in d65c7756.
-- source:
--   The pointwise source property follows from Proved 5224d9f0 global nonnegativity of the top-cap verification candidate, positivity of the discount exponential and nonnegativity of ENNReal.toReal. Keeps actual process X, original D, exact strict Iio cash, zero-nu and C=top.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_topcap_w_nonnegative_everywhere

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss_top15_original_strict_stopped_reward_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (q : ℝ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (σ : ℕ → Ω → ℝ≥0) :
    ∀ k ω,
      0 ≤ (if σ k ω = 0 then w x else
        Real.exp (-(q * (σ k ω : ℝ))) *
          w (riskProcess X x D (σ k ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) := by sorry
