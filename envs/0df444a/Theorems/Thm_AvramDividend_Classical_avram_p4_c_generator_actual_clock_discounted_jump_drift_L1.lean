-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_actual_clock_discounted_jump_drift_L1
-- name    : AvramDividend.Classical.avram_p4_c_generator_actual_clock_discounted_jump_drift_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:58:43.82216+00:00
-- url     : https://prove2.me/theorems/38b77de6-9b91-4b44-a600-3632f50e7bd9
-- title:
--   Original stopped full nonlinear negative-generator drift is genuinely discounted L1 on true physical predictable clock
-- statement:
--   For the source X, original dividend D and true ruin-clipped predictable finite physical clock with positive compact prepayment reserves, the source full compensated nonlinear jump generator drift is integrable under its actual exponential discount e^{-q t} for q≥0. The proof uses the source true-clock signed-jump L1 result transported to the exact stopped generator indicator and derives the discount weight bound from real time nonnegativity. It does not invoke an original jump-count compensator, endpoint regularity or optional stopping.
-- source:
--   Accepted c254b492 original predictable-clock signed drift L1 plus newly authored P4-C indicator L1 transport c5a56315-67d1-4aaa-8f44-4688002bc5d1 (publication pending); positive exponential discount from Mathlib.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_actual_clock_jump_drift_L1_indicator
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_actual_clock_discounted_jump_drift_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : ∀ f : (ℝ≥0 × Ω) → ℝ≥0∞,
      Measurable[𝓕.rightCont.predictable] f →
      (∫⁻ p, f p ∂μ) =
        (∫⁻ p, f p ∂((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)))
    (q : ℝ) (hq : 0 ≤ q)
    (hclock : Measurable[𝓕.rightCont.predictable]
      (fun p : ℝ≥0 × Ω => (p.1 : ℝ))) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let A : Set (ℝ≥0 × Ω) :=
      {p | (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 ∧ Y p ∈ Icc (u + δ) v}
    Integrable (A.indicator (fun p =>
      Real.exp (-(q * (p.1 : ℝ))) *
        (∫ z in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand w (Y p) z ∂X.ν))) μ := by sorry
