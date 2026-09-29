-- Prove2me | solution 1 for finite_linear_gaps_stable
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T17:31:42.049717+00:00
-- url     : https://prove2.me/submissions/f56c9baf-2401-4b66-99f6-7572216b9b79

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
The finite-dimensional Holder/triangle-inequality step used in
Lattimore--Szepesvari, *Bandit Algorithms*, Theorem 37.12, Step 3,
printed p.490: finitely many strictly positive linear gaps remain at least
half as large after a sufficiently small perturbation.
-/

theorem finite_linear_gaps_stable
    {C I : Type*} [Fintype C] [Fintype I]
    (A : C → I → ℝ) (u q : I → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ c : C, ε ≤ ∑ i, A c i * u i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Δ : ℝ, |Δ| ≤ δ → ∀ c : C,
      ε / 2 ≤ ∑ i, A c i * (u i + Δ * q i) := by
  classical
  let B : ℝ := 1 + ∑ c : C, ∑ i : I, |A c i * q i|
  have hB : 0 < B := by
    dsimp [B]
    positivity
  let δ := ε / (2 * B)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hB)
  refine ⟨δ, hδ, ?_⟩
  intro Δ hΔ c
  have hdot_abs : |∑ i : I, A c i * q i| ≤ B := by
    calc
      |∑ i : I, A c i * q i| ≤ ∑ i : I, |A c i * q i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ c' : C, ∑ i : I, |A c' i * q i| := by
        have hn : ∀ c' ∈ (Finset.univ : Finset C),
            0 ≤ ∑ i : I, |A c' i * q i| := by
          intro c' _
          positivity
        exact Finset.single_le_sum hn (Finset.mem_univ c)
      _ ≤ B := by dsimp [B]; linarith
  have hpert : -(ε / 2) ≤ Δ * ∑ i : I, A c i * q i := by
    have hprodabs : |Δ * ∑ i : I, A c i * q i| ≤ ε / 2 := by
      rw [abs_mul]
      calc
        |Δ| * |∑ i : I, A c i * q i| ≤ δ * B := by
          exact mul_le_mul hΔ hdot_abs (abs_nonneg _) hδ.le
        _ = ε / 2 := by
          dsimp [δ]
          field_simp
    exact (neg_le_neg hprodabs).trans
      (neg_abs_le (Δ * ∑ i : I, A c i * q i))
  have hid : (∑ i : I, A c i * (u i + Δ * q i)) =
      (∑ i : I, A c i * u i) + Δ * ∑ i : I, A c i * q i := by
    calc
      _ = ∑ i : I, (A c i * u i + Δ * (A c i * q i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]
  rw [hid]
  linarith [hgap c]

theorem solution
    {C I : Type*} [Fintype C] [Fintype I]
    (A : C → I → ℝ) (u q : I → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ c : C, ε ≤ ∑ i, A c i * u i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Δ : ℝ, |Δ| ≤ δ → ∀ c : C,
      ε / 2 ≤ ∑ i, A c i * (u i + Δ * q i) :=
  finite_linear_gaps_stable A u q ε hε hgap
