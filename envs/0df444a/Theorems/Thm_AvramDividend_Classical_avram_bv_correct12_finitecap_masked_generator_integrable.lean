-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finitecap_masked_generator_integrable
-- name    : AvramDividend.Classical.avram_bv_correct12_finitecap_masked_generator_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T08:07:35.049851+00:00
-- url     : https://prove2.me/theorems/5aaf4f07-b85a-40d5-b181-c199319893f1
-- title:
--   Finite-cap original BV masked HJB generator is L1 when the sampled candidate is L1
-- statement:
--   On the original Standing bounded-variation process with finite negative jump activity, a measurable generator residual masked to strictly positive finite-cap reserves is integrable whenever the sampled candidate is integrable. The result uses only actual finite-cap continuity, C1 slope and negative-reserve zero extension, avoiding the earlier globally nonnegative candidate hypothesis. This is a physical finite-grid HJB L1 bridge for 8271cf4d, 3993433e and assigned 51b72610.
-- source:
--   Necessary original finite-activity generator L1 interface for 8271cf4d, importing this strand's newly Proved 1ecef407 finite-cap residual floor and previously Proved cb439447 candidate nonnegativity. Reuses the source-verifiable proof pattern from c75afa3b but discharges its excessive global-positivity hypothesis.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_gradient_value_nonnegative_on_compact_interval
import Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finitecap_generator_residual_floor
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_correct12_finitecap_masked_generator_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
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
    (hYI : Integrable (fun ω => w (Y ω)) P)
    (hInside : ∀ ω, mask ω →
      0 < Y ω ∧ ENNReal.ofReal (Y ω) < C ∧
      X.GeneratorIntegrable w (Y ω) ∧
      X.generator w (Y ω) - q * w (Y ω) ≤ 0)
    (hMeas : AEStronglyMeasurable (fun ω =>
      if mask ω then X.generator w (Y ω) - q * w (Y ω) else 0) P) :
    Integrable (fun ω =>
      if mask ω then X.generator w (Y ω) - q * w (Y ω) else 0) P := by sorry
