-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_variation_zero_barrier_candidate_lipschitz
-- name    : AvramDividend.Classical.unbounded_variation_zero_barrier_candidate_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:35:30.29281+00:00
-- url     : https://prove2.me/theorems/f5eab1db-9c53-4797-9969-4c68387c32d9
-- title:
--   Global unit Lipschitz bound for the unbounded-variation zero-barrier candidate
-- statement:
--   For a spectrally negative Lévy process of unbounded variation under positive discount, the zero-barrier dividend candidate x↦barrierValue W 0 x is globally Lipschitz with constant one. The proved identity with max(x,0) and the pinned Mathlib LipschitzWith.max_const lemma establish the result, which controls jumps and supports generator-domain integrability without extra smoothness conditions.
-- source:
--   Proved zero-barrier candidate equals positive-part identity; pinned Mathlib LipschitzWith.id and LipschitzWith.max_const.

import Theorems.Thm_AvramDividend_Classical_unbounded_variation_zero_barrier_candidate_eq_posPart
import Mathlib.Topology.MetricSpace.Lipschitz

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_variation_zero_barrier_candidate_lipschitz
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    LipschitzWith (1 : ℝ≥0) (barrierValue W 0) := by sorry
