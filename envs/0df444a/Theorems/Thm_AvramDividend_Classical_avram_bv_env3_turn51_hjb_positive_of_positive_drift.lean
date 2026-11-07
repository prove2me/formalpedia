-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn51_hjb_positive_of_positive_drift
-- name    : AvramDividend.Classical.avram_bv_env3_turn51_hjb_positive_of_positive_drift
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T10:01:20.215038+00:00
-- url     : https://prove2.me/theorems/59f64444-d6c7-4dbc-93ac-c859f69f9b80
-- title:
--   Original BV HJB supersolution with positive drift has strictly positive initial value
-- statement:
--   For the actual bounded-variation spectrally negative Lévy generator with strictly positive BV drift, any nonnegative C1 gradient-dominating HJB supersolution has strictly positive value at every nonnegative capital below a positive cap. At positive capital the known strict secant inequality suffices; at zero, integrate the compensated negative jump generator over a vanishing positive interval and exploit the finite-variation small-jump first moment to contradict positive drift if w(0)=0.
-- source:
--   Source-exact BV generator; bounded variation ∫_{(-1,0)} |z| ν(dz) < ∞; exact drift = c - ∫ z ν; strict interior HJB; gradient ≥ 1; continuity at the origin. The source-exact translation identity ∫_0^ε (w(y)-w(y-a)) dy = ∫_{max(0,ε-a)}^ε w(y) dy controls negative jumps by ∫ min(ε,-z) ν(dz), which vanishes as ε↓0. This is the independent analytical zero-benchmark obstruction that removes the entire be711acd branch from the parent, conditional on proving this new child. No original stochastic stopped-grid premise is assumed or replaced.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn51_hjb_positive_of_positive_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (hDrift : 0 < X.drift) :
    0 < w x := by sorry
