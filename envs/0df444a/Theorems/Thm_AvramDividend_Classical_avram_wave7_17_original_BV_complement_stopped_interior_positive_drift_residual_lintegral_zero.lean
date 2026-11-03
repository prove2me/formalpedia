-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_complement_stopped_interior_positive_drift_residual_lintegral_zero
-- name    : AvramDividend.Classical.avram_wave7_17_original_BV_complement_stopped_interior_positive_drift_residual_lintegral_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:17:57.974278+00:00
-- url     : https://prove2.me/theorems/eb3cbab8-a15c-4a7b-bebe-485883f6ac45
-- title:
--   Original strict-complement BV stopped interior has zero positive discounted physical drift minus compensated negative-jump generator mass
-- statement:
--   For the genuine original BV Levy X, filtration and admissible D, the positive part of the discounted physical drift plus actual negative-mark generator integral minus q-times-candidate value has exactly zero ENNReal physical time × probability mass on the ruin-stopped interior. The result needs only measurability of the actual interior set; no L1 hypothesis on the unbounded generator correction. It follows from the proved original strict-complement positive physical drift and W7-02 original predictable-state discounted HJB sign. It does not assert an Ito-Meyer compensation identity or zero occupation at reserve zero or the cap.
-- source:
--   Avram-Palmowski-Pistorius (2007), Proposition 4(i), bounded-variation drift/jump generator HJB residual on the actual stopped interior. Uses Proved strict complement d6705e01 and Proved source predictable HJB envelope a0879a2f. Stronger than an L1-restricted inequality for the positive residual and useful for localisation, but not itself a cash HJB bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_strict_complement_sharp_drift_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_predictable_discounted_generator_gradient_envelope
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_17_original_BV_complement_stopped_interior_positive_drift_residual_lintegral_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ) (hH : 0 ≤ H)
    (hEnvelope : ¬ (x + H * X.drift ≤ w x))
    (T : ℝ≥0) :
    let μ : Measure (ℝ≥0 × Ω) :=
      ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim (fun t : ℝ≥0 =>
        x + X.X t p.2 - rightLimit D t p.2) p.1
    let S : Set (ℝ≥0 × Ω) :=
      {p | p.1 ≤ T ∧ (p.1 : ℝ≥0∞) < ruinTime X x D p.2 ∧
        0 < Y p ∧ ENNReal.ofReal (Y p) < C}
    MeasurableSet S →
    (∫⁻ p in S, ENNReal.ofReal
      (Real.exp (-(q * (p.1 : ℝ))) *
        (X.drift + (∫ z in Iio (0 : ℝ),
          w (Y p + z) - w (Y p) ∂X.ν) - q * w (Y p))) ∂μ) = 0 := by sorry
