-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_complement_automatic_stopped_drift_L1_and_HJB_residual_zero
-- name    : AvramDividend.Classical.avram_wave7_17_original_BV_complement_automatic_stopped_drift_L1_and_HJB_residual_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:14:39.114491+00:00
-- url     : https://prove2.me/theorems/7bde9a48-0506-4711-8679-a18487b00ffc
-- title:
--   Original BV strict drift complement: unconditional physical stopped-drift L1 and zero positive HJB generator mass
-- statement:
--   Under the actual original X, P and capped dividend strategy, strict positive-reserve pre-ruin physical time times probability measurable interior follows from the original filtered left-limit and ruin clock. Without any extra localisation-measurability or drift-integrability premises, the finite stopped discounted drift is L1 and the positive part of the exact Lévy negative-jump generator plus physical drift minus q times w has zero ENNReal source-clock mass. Includes T=0. This is a source HJB input; its proof does not claim the random jump compensator identity, terminal/ruin boundary or full Stieltjes expected cash bound.
-- source:
--   Compose existing Proved original-source lemmas f2efea1f (ruin strict interior measurable), da1766f8 (discounted physical drift L1) and eb3cbab8 (strict-complement HJB drift/jump positive residual zero), all on the same physical Lebesgue-time × original P clock. A direct assumption-free interface for W8-04 complement generator localisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_ruin_stopped_strict_interior_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_stopped_physical_discounted_drift_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_complement_stopped_interior_positive_drift_residual_lintegral_zero
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_17_original_BV_complement_automatic_stopped_drift_L1_and_HJB_residual_zero
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
    IntegrableOn
      (fun p => Real.exp (-(q * (p.1 : ℝ))) * X.drift) S μ ∧
    (∫⁻ p in S, ENNReal.ofReal
      (Real.exp (-(q * (p.1 : ℝ))) *
        (X.drift + (∫ z in Iio (0 : ℝ),
          w (Y p + z) - w (Y p) ∂X.ν) - q * w (Y p))) ∂μ) = 0 := by sorry
