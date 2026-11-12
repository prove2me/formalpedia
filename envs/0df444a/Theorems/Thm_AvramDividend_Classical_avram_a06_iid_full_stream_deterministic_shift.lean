-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_iid_full_stream_deterministic_shift
-- name    : AvramDividend.Classical.avram_a06_iid_full_stream_deterministic_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T08:36:17.248262+00:00
-- url     : https://prove2.me/theorems/c5ed4147-cea0-4e70-b261-f32dfb167a16
-- title:
--   Deterministic shift of an entire iid exponential renewal stream preserves its joint law
-- statement:
--   The whole future infinite sequence of iid interarrival times beginning at any fixed index has the same product distribution as the initial infinite sequence.
-- source:
--   Reindex iIndepFun by an injective tail shift, infer product-law HasLaw for both infinite sequences, conclude IdentDistrib.

import Mathlib
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_iid_full_stream_deterministic_shift
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hiid : iIndepFun τ P)
    (μ : Measure ℝ)
    (hLaw : ∀ n, HasLaw (τ n) μ P)
    (m : ℕ) :
    IdentDistrib (fun ω (j : ℕ) => τ (m + j) ω)
      (fun ω (j : ℕ) => τ j ω) P P := by sorry
