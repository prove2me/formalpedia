-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_positive_supremum_tail_extend
-- name    : AvramDividend.Classical.avram_ws01e_bf_new_positive_supremum_tail_extend
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:00:49.865579+00:00
-- url     : https://prove2.me/theorems/4bd8f522-5792-4eba-8153-a4e1c9576430
-- title:
--   Strictly positive supremum extends one test's nonnegative upper-ray factor to all real cutoffs
-- statement:
--   Under an arbitrary measure μ and one ENNReal weight W, if S is strictly positive μ-almost everywhere, its upper-ray weighted-mass factorisation for b≥0 extends to every real threshold. For b<0 the upper-ray events {b<S} and {0<S} agree almost everywhere under μ and under the absolutely continuous weighted measure μ.withDensity W. This proves only a fixed weighted-tail formula, not full stochastic independence. Used only as a possible single-test route for descending factorisation from the already Proved Chat 01 threshold identity.
-- source:
--   Elementary measure-congruence and absolute continuity of withDensity in pinned Mathlib; no process-specific stochastic assertion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bf_new_positive_supremum_tail_extend
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) (W : Ω → ENNReal)
    (hSpos : ∀ᵐ z ∂μ, 0 < S z)
    (hPos : ∀ b : ℝ, 0 ≤ b →
      (μ.withDensity W) {z : Ω | b < S z} =
        μ {z : Ω | b < S z} * (∫⁻ z, W z ∂μ)) :
    ∀ b : ℝ,
      (μ.withDensity W) {z : Ω | b < S z} =
        μ {z : Ω | b < S z} * (∫⁻ z, W z ∂μ) := by sorry
