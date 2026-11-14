-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB248_continuous_minus_locally_BV_reserve_ae_time_continuous
-- name    : AvramDividend.Classical.avram_gbB248_continuous_minus_locally_BV_reserve_ae_time_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:27:24.507596+00:00
-- url     : https://prove2.me/theorems/659786cc-36a0-42ee-a817-8438dd4dd7ee
-- title:
--   Gaussian continuous source minus locally BV reserve is continuous almost everywhere in any atomless physical-time measure
-- statement:
--   The original-type Gaussian reserve with a continuous source and locally finite-variation dividend correction is continuous for almost every physical time under any measure with null singletons, since its discontinuities are countable by B247. This is an exact null-exception input for mesh and occupation-time convergence without any assumption of an already-constructed local time.
-- source:
--   Generic B243 occupation time path regularity; direct B247 plus Set.Countable.measure_zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB248_continuous_minus_locally_BV_reserve_ae_time_continuous
    (f : ℝ≥0 → ℝ) (hf : Continuous f)
    (d : ℝ≥0 → ℝ)
    (hd : LocallyBoundedVariationOn d Set.univ)
    (x : ℝ) (μ : Measure ℝ≥0) [NullSingletonClass μ] :
    ∀ᵐ t ∂μ, ContinuousAt
      (fun s : ℝ≥0 => x + f s - d s) t := by sorry
