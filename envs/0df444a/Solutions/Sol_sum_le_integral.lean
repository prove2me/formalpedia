-- Prove2me | solution 1 for sum_le_integral
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:30:42.332379+00:00
-- url     : https://prove2.me/submissions/329cb661-135a-4448-b11f-f4d0176a4d97

import Mathlib.Analysis.SumIntegralComparisons

open Real BigOperators MeasureTheory Set intervalIntegral

theorem solution {x₀ : ℝ} {f : ℝ → ℝ} {n : ℕ} (hf : AntitoneOn f (Ioc x₀ (x₀ + n)))
    (hfi : IntegrableOn f (Icc x₀ (x₀ + n))) :
    (∑ i ∈ Finset.range n, f (x₀ + ↑(i + 1))) ≤ ∫ x in x₀..x₀ + n, f x := by
  have hfi' (k : ℕ) (hk : k + 1 ≤ n) :
      IntervalIntegrable f volume (x₀ + k) (x₀ + ↑(k + 1)) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by simp)]
    apply hfi.mono _ le_rfl
    apply Icc_subset_Icc <;> simp [-Nat.cast_add, hk]
  calc
    _ = ∑ i ∈ Finset.range n, ∫ _ in x₀ + i..x₀ + ↑(i + 1), f (x₀ + ↑(i + 1)) := by simp
    _ ≤ ∑ i ∈ Finset.range n, ∫ x in x₀ + i..x₀ + ↑(i + 1), f x := by
      gcongr with i hi
      rw [Finset.mem_range, ← Nat.add_one_le_iff] at hi
      have hint := hfi' i hi
      rify at hi hint ⊢
      exact integral_mono_on_of_le_Ioo (by simp) (by simp) hint fun x hx ↦ by
        apply hf <;> grind
    _ = _ := by
      convert! sum_integral_adjacent_intervals hfi'
      simp [-Nat.cast_add]
