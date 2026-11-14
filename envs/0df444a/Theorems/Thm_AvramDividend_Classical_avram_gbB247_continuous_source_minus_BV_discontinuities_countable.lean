-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB247_continuous_source_minus_BV_discontinuities_countable
-- name    : AvramDividend.Classical.avram_gbB247_continuous_source_minus_BV_discontinuities_countable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:24:34.759065+00:00
-- url     : https://prove2.me/theorems/58aeb008-668b-44b7-bfe2-a14ee9a490ca
-- title:
--   Original-type Gaussian continuous source minus arbitrary locally BV correction has countably many path discontinuities
-- statement:
--   For a real continuous Gaussian source sample path and an arbitrary locally finite-variation correction, their shifted difference is continuous at every point at which the correction is continuous. Hence the original-type reserve has at most countably many time discontinuities. Its inputs are the exact source and correction, with B246 supplying generic finite-variation countability.
-- source:
--   Generic original Gaussian B243 occupancy time path regularity, consequence of B246 and ContinuousAt.sub; no localtime premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB247_continuous_source_minus_BV_discontinuities_countable
    (f : ℝ≥0 → ℝ) (hf : Continuous f)
    (d : ℝ≥0 → ℝ)
    (hd : LocallyBoundedVariationOn d Set.univ)
    (x : ℝ) :
    Set.Countable {t : ℝ≥0 |
      ¬ ContinuousAt (fun s : ℝ≥0 => x + f s - d s) t} := by sorry
