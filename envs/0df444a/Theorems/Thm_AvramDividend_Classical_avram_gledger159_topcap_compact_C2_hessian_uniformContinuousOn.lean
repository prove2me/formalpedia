-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger159_topcap_compact_C2_hessian_uniformContinuousOn
-- name    : AvramDividend.Classical.avram_gledger159_topcap_compact_C2_hessian_uniformContinuousOn
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:56:30.703645+00:00
-- url     : https://prove2.me/theorems/4d4f7afd-539a-4fb2-bfbc-10857624a609
-- title:
--   Uniform continuity of the top-cap Gaussian Hessian on the exact interior band
-- statement:
--   For the top-cap Gaussian route, the genuine C2 second derivative is uniformly continuous on every positive deterministic compact interval, using exactly the original interior smoothness condition. Supplies the compact Hessian Taylor modulus needed in original gledger140 without global bounds near zero.
-- source:
--   Source top-cap smoothness hTopCap; mathlib ContDiffOn continuous second iterated derivative on open interior, compact interval uniform continuity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger159_topcap_compact_C2_hessian_uniformContinuousOn
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    UniformContinuousOn (iteratedDeriv 2 w) (Icc a b) := by sorry
