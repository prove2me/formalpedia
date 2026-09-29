-- Prove2me | solution 1 for tangent_coordinate_kernel_diagonal_bound_from_singular_coordinate_energies
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T17:17:49.953414+00:00
-- url     : https://prove2.me/submissions/40ff5466-567e-4318-a3a3-0a46be82efe9

import Mathlib.Tactic
import Definitions.Def_matrix_completion_neumann

open MatrixCompletion

open scoped Classical BigOperators

private lemma matrixInner_coordinate_right
    {n₁ n₂ : ℕ} (X : Matrix (Fin n₁) (Fin n₂) ℝ)
    (i : Fin n₁) (j : Fin n₂) :
    matrixInner X (coordinateMatrix i j) = X i j := by
  unfold matrixInner coordinateMatrix
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _hb hb
      simp [hb]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  · intro a _ha ha
    simp [ha]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private lemma leftSingularProjection_coordinate_same
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂) :
    leftSingularProjection S (coordinateMatrix i j) i j =
      ∑ k : Fin r, (S.u k i) ^ 2 := by
  unfold leftSingularProjection coordinateMatrix
  rw [Finset.sum_eq_single i]
  · simp [pow_two]
  · intro a _ha ha
    simp [ha]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private lemma rightSingularProjection_coordinate_same
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂) :
    rightSingularProjection S (coordinateMatrix i j) i j =
      ∑ k : Fin r, (S.v k j) ^ 2 := by
  unfold rightSingularProjection coordinateMatrix
  rw [Finset.sum_eq_single j]
  · simp [pow_two]
  · intro b _hb hb
    simp [hb]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

private lemma twoSidedSingularProjection_coordinate_same
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂) :
    twoSidedSingularProjection S (coordinateMatrix i j) i j =
      (∑ k : Fin r, (S.u k i) ^ 2) *
        (∑ k : Fin r, (S.v k j) ^ 2) := by
  unfold twoSidedSingularProjection coordinateMatrix
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp [pow_two, Finset.mul_sum, Finset.sum_mul]
    · intro b _hb hb
      simp [hb]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  · intro a _ha ha
    simp [ha]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private lemma tangent_coordinate_kernel_diagonal_formula
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂) :
    tangentCoordinateKernel S i j i j =
      (∑ k : Fin r, (S.u k i) ^ 2) +
        (∑ k : Fin r, (S.v k j) ^ 2) -
          (∑ k : Fin r, (S.u k i) ^ 2) *
            (∑ k : Fin r, (S.v k j) ^ 2) := by
  rw [tangentCoordinateKernel, matrixInner_coordinate_right]
  simp [tangentProjection, leftSingularProjection_coordinate_same,
    rightSingularProjection_coordinate_same,
    twoSidedSingularProjection_coordinate_same]

/-- The diagonal tangent-kernel estimate follows from coordinate-energy bounds
for the two singular-vector spaces and the Bessel bounds that those energies
are at most one. -/
theorem solution :
    ∃ Cker : ℝ, 0 < Cker ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ →
        (∀ i : Fin n₁,
          ∑ k : Fin r, (S.u k i) ^ 2 ≤ μ₀ * (r : ℝ) / (n₁ : ℝ)) →
        (∀ j : Fin n₂,
          ∑ k : Fin r, (S.v k j) ^ 2 ≤ μ₀ * (r : ℝ) / (n₂ : ℝ)) →
        (∀ i : Fin n₁, ∑ k : Fin r, (S.u k i) ^ 2 ≤ (1 : ℝ)) →
        (∀ j : Fin n₂, ∑ k : Fin r, (S.v k j) ^ 2 ≤ (1 : ℝ)) →
        ∀ i j,
          |tangentCoordinateKernel S i j i j| ≤
            Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by
  refine ⟨3, by norm_num, ?_⟩
  intro n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hu hv huOne hvOne i j
  let U : ℝ := ∑ k : Fin r, (S.u k i) ^ 2
  let V : ℝ := ∑ k : Fin r, (S.v k j) ^ 2
  let scale : ℝ := μ₀ * (r : ℝ) / (((min n₁ n₂ : ℕ) : ℝ))
  have hmin_pos_nat : 0 < min n₁ n₂ := lt_min hn₁ hn₂
  have hscale_nonneg : 0 ≤ scale := by
    dsimp [scale]
    positivity
  have hU_nonneg : 0 ≤ U := by
    dsimp [U]
    exact Finset.sum_nonneg fun k _ => sq_nonneg (S.u k i)
  have hV_nonneg : 0 ≤ V := by
    dsimp [V]
    exact Finset.sum_nonneg fun k _ => sq_nonneg (S.v k j)
  have hU_one : U ≤ 1 := by
    simpa [U] using huOne i
  have hV_one : V ≤ 1 := by
    simpa [V] using hvOne j
  have hU_scale : U ≤ scale := by
    have hmin_le : (((min n₁ n₂ : ℕ) : ℝ)) ≤ (n₁ : ℝ) := by
      exact_mod_cast min_le_left n₁ n₂
    have hmono :
        μ₀ * (r : ℝ) / (n₁ : ℝ) ≤
          μ₀ * (r : ℝ) / (((min n₁ n₂ : ℕ) : ℝ)) := by
      gcongr
    exact le_trans (by simpa [U] using hu i) hmono
  have hV_scale : V ≤ scale := by
    have hmin_le : (((min n₁ n₂ : ℕ) : ℝ)) ≤ (n₂ : ℝ) := by
      exact_mod_cast min_le_right n₁ n₂
    have hmono :
        μ₀ * (r : ℝ) / (n₂ : ℝ) ≤
          μ₀ * (r : ℝ) / (((min n₁ n₂ : ℕ) : ℝ)) := by
      gcongr
    exact le_trans (by simpa [V] using hv j) hmono
  have hformula := tangent_coordinate_kernel_diagonal_formula S i j
  have hnonneg_expr : 0 ≤ U + V - U * V := by
    have h1V : 0 ≤ 1 - V := by linarith
    nlinarith [mul_nonneg hU_nonneg h1V, hV_nonneg]
  calc
    |tangentCoordinateKernel S i j i j|
        = |U + V - U * V| := by
          rw [hformula]
    _ = U + V - U * V := abs_of_nonneg hnonneg_expr
    _ ≤ U + V := by nlinarith [mul_nonneg hU_nonneg hV_nonneg]
    _ ≤ scale + scale := by linarith
    _ ≤ 3 * scale := by nlinarith [hscale_nonneg]
    _ = 3 * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by
      dsimp [scale]
      ring
