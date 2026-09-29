-- Prove2me | solution 1 for quadratic_neumann_first_index_distinct_mean_coefficient_from_off_diagonal_response_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T15:20:18.659384+00:00
-- url     : https://prove2.me/submissions/8aa11658-a7a5-408b-bf59-3d3323e6fbaa

import Mathlib.Data.Fintype.Order
import Definitions.Def_matrix_completion_neumann

open MatrixCompletion

private lemma entrySupNorm_le_of_forall_abs_le {n₁ n₂ : ℕ}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (B : ℝ)
    (h : ∀ i j, |X i j| ≤ B) :
    entrySupNorm X ≤ B := by
  haveI : Nonempty (Fin n₁) := Fin.pos_iff_nonempty.mp hn₁
  haveI : Nonempty (Fin n₂) := Fin.pos_iff_nonempty.mp hn₂
  unfold entrySupNorm
  exact ciSup_le fun i => ciSup_le fun j => h i j

private lemma abs_entry_le_entrySupNorm {n₁ n₂ : ℕ}
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (i : Fin n₁) (j : Fin n₂) :
    |X i j| ≤ entrySupNorm X := by
  unfold entrySupNorm
  exact Finite.le_ciSup_of_le i (Finite.le_ciSup_of_le j le_rfl)

private lemma entrySupNorm_smul_le_of_nonneg {n₁ n₂ : ℕ}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (c : ℝ) (hc : 0 ≤ c) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    entrySupNorm (c • X) ≤ c * entrySupNorm X := by
  apply entrySupNorm_le_of_forall_abs_le hn₁ hn₂
  intro i j
  calc
    |(c • X) i j| = |c| * |X i j| := by
      simp [abs_mul]
    _ = c * |X i j| := by rw [abs_of_nonneg hc]
    _ ≤ c * entrySupNorm X := by
      exact mul_le_mul_of_nonneg_left (abs_entry_le_entrySupNorm X i j) hc

theorem solution
    (Cresp : ℝ) :
    0 < Cresp →
    ∃ Ccoef : ℝ, 0 < Ccoef ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r) (p : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → 0 < p →
        1 ≤ μ₀ → A0 S μ₀ →
        quadraticFirstIndexDistinctMeanCoefficientMatrix S p =
          p⁻¹ • offDiagonalTangentResponse S
            (linearNeumannDiagonalBaseMatrix S) →
        entrySupNorm (offDiagonalTangentResponse S
          (linearNeumannDiagonalBaseMatrix S)) ≤
          Cresp * μ₀ ^ 2 *
            (((r : ℝ) / (↑(max n₁ n₂))) ^ 2) →
        entrySupNorm (quadraticFirstIndexDistinctMeanCoefficientMatrix S p) ≤
          Ccoef * μ₀ ^ 2 *
            (((r : ℝ) / (↑(max n₁ n₂))) ^ 2) * p⁻¹ := by
  intro hCresp
  refine ⟨Cresp, hCresp, ?_⟩
  intro n₁ n₂ r M μ₀ S p hn₁ hn₂ _hr hp _hμ₀ _hA0 hrep hresp
  rw [hrep]
  calc
    entrySupNorm (p⁻¹ • offDiagonalTangentResponse S
        (linearNeumannDiagonalBaseMatrix S))
        ≤ p⁻¹ *
            entrySupNorm (offDiagonalTangentResponse S
              (linearNeumannDiagonalBaseMatrix S)) :=
          entrySupNorm_smul_le_of_nonneg hn₁ hn₂ p⁻¹
            (inv_nonneg.mpr (le_of_lt hp))
            (offDiagonalTangentResponse S (linearNeumannDiagonalBaseMatrix S))
    _ ≤ p⁻¹ *
          (Cresp * μ₀ ^ 2 * (((r : ℝ) / (↑(max n₁ n₂))) ^ 2)) := by
          exact mul_le_mul_of_nonneg_left hresp (inv_nonneg.mpr (le_of_lt hp))
    _ = Cresp * μ₀ ^ 2 * (((r : ℝ) / (↑(max n₁ n₂))) ^ 2) * p⁻¹ := by
          ring
