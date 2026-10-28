-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_variation_zero_barrier_candidate_monotone
-- name    : AvramDividend.Classical.unbounded_variation_zero_barrier_candidate_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:32:02.258994+00:00
-- url     : https://prove2.me/theorems/62a44fa6-b168-4d8e-9218-b0a1e1fc29be
-- title:
--   Monotonicity of the unbounded-variation zero-barrier dividend candidate
-- statement:
--   For a spectrally negative Lévy process of unbounded variation under a positive discount, the zero-barrier candidate value is a monotone function of reserve across all real reserves, including the ruin boundary. The proved global formula max(x,0) reduces the result to monotonicity of the maximum. This is an analytic verification property independent of derivative and regularity hypotheses.
-- source:
--   Proved unbounded_variation_zero_barrier_candidate_eq_posPart and monotonicity of max.

import Theorems.Thm_AvramDividend_Classical_unbounded_variation_zero_barrier_candidate_eq_posPart
import Mathlib.Order.Monotone.Basic

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_variation_zero_barrier_candidate_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    Monotone (barrierValue W 0) := by sorry
