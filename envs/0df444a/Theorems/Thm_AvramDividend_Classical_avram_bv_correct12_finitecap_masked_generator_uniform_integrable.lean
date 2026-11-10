-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finitecap_masked_generator_uniform_integrable
-- name    : AvramDividend.Classical.avram_bv_correct12_finitecap_masked_generator_uniform_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T08:52:52.715196+00:00
-- url     : https://prove2.me/theorems/0eff1db7-1442-43a6-bf62-01937cc2f72f
-- title:
--   Original finite-cap BV HJB generator is L1 from a bounded masked candidate, without unmasked sampling
-- statement:
--   Original finite-cap BV masked HJB generator residuals are integrable when their signed HJB sign, interior location, measurability and finite-cap candidate bound hold. No integrability or boundedness of the unmasked candidate is required: the physical prepayment reserve may become negative or lie outside the cap on paths removed by the mask. Finite activity and the source-exact 1ecef407 residual floor dominate the masked generator by a deterministic integrable constant. For 8271cf4d and 3993433e.
-- source:
--   Necessary root-connected finite-activity L1 bridge for 8271cf4d. Corrects the excessive unmasked w(Y) integrability hypothesis in 5aaf4f07. Use existing Proved 00de5b03 to obtain a finite value bound R on the original finite-cap interior mask; source-exact bound 1ecef407 controls the HJB residual and shows L1 without assumptions on excluded paths.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_gradient_value_nonnegative_on_compact_interval
import Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finitecap_generator_residual_floor
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_correct12_finitecap_masked_generator_uniform_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ z < 0, w z = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C →
      1 ≤ deriv w z)
    (hMass : X.ν (Iio (0 : ℝ)) < ⊤)
    (Y : Ω → ℝ) (mask : Ω → Prop)
    (R : ℝ) (hR : 0 ≤ R)
    (hValueBound : ∀ ω, mask ω → w (Y ω) ≤ R)
    (hInside : ∀ ω, mask ω →
      0 < Y ω ∧ ENNReal.ofReal (Y ω) < C ∧
      X.GeneratorIntegrable w (Y ω) ∧
      X.generator w (Y ω) - q * w (Y ω) ≤ 0)
    (hMeas : AEStronglyMeasurable (fun ω =>
      if mask ω then X.generator w (Y ω) - q * w (Y ω) else 0) P) :
    Integrable (fun ω =>
      if mask ω then X.generator w (Y ω) - q * w (Y ω) else 0) P := by sorry
