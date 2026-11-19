-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva47_counting_measure_false_signed_L1_source_counterexample
-- name    : AvramDividend.Classical.avram_bva47_counting_measure_false_signed_L1_source_counterexample
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T07:30:30.77137+00:00
-- url     : https://prove2.me/theorems/b3fbb649-bb12-4526-8c80-05a82574ebf1
-- title:
--   Explicit infinite-counting-measure counterexample to the original non-probability signed source L1 implication
-- statement:
--   There exist strongly measurable signed drift and three integrable source terms under an infinite counting measure, with nonpositive drift and a pointwise HJB-style upper source inequality, even though the signed drift is not integrable. Explicitly take counting measure on the natural numbers, F=M=E=0, B=-1 and a=1. Then F≤a+M+B+E_+ holds as equality everywhere, while B has infinite absolute integral. This formally demonstrates the missing finite-measure assumption in the earlier invalid original bva43 candidate and supports the Proved probability-space correction bva44.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.NormNum
set_option autoImplicit false
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva47_counting_measure_false_signed_L1_source_counterexample :
    ∃ (F M B E : ℕ → ℝ) (a : ℝ),
      Integrable F (Measure.count : Measure ℕ) ∧
      Integrable M (Measure.count : Measure ℕ) ∧
      Integrable (fun ω => max (E ω) 0) (Measure.count : Measure ℕ) ∧
      AEStronglyMeasurable B (Measure.count : Measure ℕ) ∧
      (∀ᵐ ω ∂(Measure.count : Measure ℕ), B ω ≤ 0) ∧
      (∀ᵐ ω ∂(Measure.count : Measure ℕ),
        F ω ≤ a + M ω + B ω + max (E ω) 0) ∧
      ¬ Integrable B (Measure.count : Measure ℕ) := by sorry
