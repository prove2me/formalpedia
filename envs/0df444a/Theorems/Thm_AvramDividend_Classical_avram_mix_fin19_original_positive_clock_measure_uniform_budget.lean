-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin19_original_positive_clock_measure_uniform_budget
-- name    : AvramDividend.Classical.avram_mix_fin19_original_positive_clock_measure_uniform_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T07:50:48.642202+00:00
-- url     : https://prove2.me/theorems/fec73bf0-dfb0-4766-85cd-c129c269a62b
-- title:
--   Uniform eventwise stopped budget from positive clock containment and finite event mass
-- statement:
--   An original stopping clock L_k bounded by σ has a subset positive-clock event, including any measurable initial event A. For finite measure P(A∩{σ>0}) and nonnegative coefficient a, a local reward upper budget a·P(A∩{L_k>0}) is bounded by the uniform terminal event budget. This analytic mass-control step is needed before the original cofinal source Fatou passage; it assumes the genuine local Itô budget as a premise.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin19_original_positive_clock_measure_uniform_budget
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (σ : Ω → ℝ≥0) (L : ℕ → Ω → ℝ≥0)
    (hLle : ∀ k ω, L k ω ≤ σ ω)
    (a : ℝ) (ha : 0 ≤ a)
    (hPfinite : P (A ∩ {ω : Ω | σ ω ≠ 0}) ≠ ⊤)
    (R : ℕ → Ω → ℝ)
    (hLocal : ∀ k,
      (∫ ω in A ∩ {η : Ω | L k η ≠ 0}, R k ω ∂P) ≤
        a * (P (A ∩ {η : Ω | L k η ≠ 0})).toReal) :
    ∀ k, (∫ ω in A ∩ {η : Ω | L k η ≠ 0}, R k ω ∂P) ≤
      a * (P (A ∩ {η : Ω | σ η ≠ 0})).toReal := by sorry
