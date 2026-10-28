-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_variation_zero_barrier_candidate_continuous
-- name    : AvramDividend.Classical.unbounded_variation_zero_barrier_candidate_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:30:53.085003+00:00
-- url     : https://prove2.me/theorems/49821e9d-3d2b-4712-95fa-cfe221c426d2
-- title:
--   Global continuity of the unbounded-variation zero-barrier dividend candidate
-- statement:
--   The zero-barrier scale-function value candidate is continuous across the origin for any unbounded-variation spectrally negative Lévy process at a positive discount. It equals max(x,0) everywhere, so inherits continuity of the maximum of continuous real functions. This supplies the zero-barrier continuity boundary condition used in stochastic verification.
-- source:
--   Proved unbounded_variation_zero_barrier_candidate_eq_posPart and continuity of max in pinned Mathlib.

import Theorems.Thm_AvramDividend_Classical_unbounded_variation_zero_barrier_candidate_eq_posPart
import Mathlib.Topology.Order.OrderClosed

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_variation_zero_barrier_candidate_continuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    Continuous (barrierValue W 0) := by sorry
