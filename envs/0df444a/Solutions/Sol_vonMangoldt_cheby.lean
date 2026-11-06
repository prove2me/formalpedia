-- Prove2me | solution 1 for vonMangoldt_cheby
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:00:05.465255+00:00
-- url     : https://prove2.me/submissions/63c283cd-9b4f-4ab1-b752-2b740b447df6

import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_PrimeNumberTheoremAnd_Wiener

open ArithmeticFunction

theorem solution : (∃ C : ℝ, ∀ n : ℕ, cumsum (fun k : ℕ ↦ ‖(Λ k : ℂ)‖) n ≤ C * n) := by
  refine ⟨Real.log 4 + 4, fun n ↦ ?_⟩
  have hψ : Chebyshev.psi (n : ℝ) =
      ∑ k ∈ Finset.range (n + 1), Λ k := by
    rw [Chebyshev.psi_eq_sum_Icc]
    simp only [Nat.floor_natCast]
    congr 1
    ext k
    simp
  calc
    cumsum (fun k : ℕ ↦ ‖(Λ k : ℂ)‖) n = ∑ k ∈ Finset.range n, Λ k := by
      unfold cumsum
      apply Finset.sum_congr rfl
      intro k _
      exact Complex.norm_of_nonneg vonMangoldt_nonneg
    _ ≤ (∑ k ∈ Finset.range n, Λ k) + Λ n :=
      le_add_of_nonneg_right vonMangoldt_nonneg
    _ = ∑ k ∈ Finset.range (n + 1), Λ k := by
      rw [Finset.sum_range_succ]
    _ = Chebyshev.psi (n : ℝ) := hψ.symm
    _ ≤ (Real.log 4 + 4) * (n : ℝ) :=
      Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n)
