-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_complement_expected_drift_jump_cover_one_L1
-- name    : AvramDividend.Classical.avram_wave7_17_original_BV_complement_expected_drift_jump_cover_one_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:26:31.300207+00:00
-- url     : https://prove2.me/theorems/fad20d8d-47ff-4f18-9244-b32ea8ee1e30
-- title:
--   Original strict BV complement expected physical drift is covered by source negative-jump generator under only the opposing-term L1 premise
-- statement:
--   For the original stopped BV process, strict drift-envelope complement and HJB assumptions, the real expectation over the original finite physical time × P strict pre-ruin positive subcap interior of discounted X.drift is bounded by the expected discounted q w minus the true negative-mark source jump generator. It needs only L1 of the latter scalar signed source integrand: original stopped measurability and the physical-drift L1 are proved automatically from admissibility and positive discount. Zero horizon is admitted. No claim of realised jump compensation or complete dividend Stieltjes bound is made.
-- source:
--   Proved W7-17 b4a4ea2a original real expected drift/jump cover, Proved f2efea1f stopped interior measurable and Proved 7bde9a48 automatic drift L1 and HJB positive residual zero. Exact one-sided local integrability bridge for W8-04/W8-22 generator expectation on original process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_ruin_stopped_strict_interior_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_complement_automatic_stopped_drift_L1_and_HJB_residual_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_complement_stopped_interior_expected_jump_drift_cover
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_17_original_BV_complement_expected_drift_jump_cover_one_L1
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
      (fun p => Real.exp (-(q * (p.1 : ℝ))) *
        (q * w (Y p) - (∫ z in Iio (0 : ℝ),
          w (Y p + z) - w (Y p) ∂X.ν))) S μ →
    (∫ p in S, Real.exp (-(q * (p.1 : ℝ))) * X.drift ∂μ) ≤
    (∫ p in S, Real.exp (-(q * (p.1 : ℝ))) *
      (q * w (Y p) - (∫ z in Iio (0 : ℝ),
        w (Y p + z) - w (Y p) ∂X.ν)) ∂μ) := by sorry
