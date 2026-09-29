-- Prove2me | solution 1 for quadratic_neumann_all_distinct_middle_base_frobenius_norm_bound_min_dim
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-01T09:51:17.58383+00:00
-- url     : https://prove2.me/submissions/22de1ebf-2064-4348-bebe-1f65a5e2ddff

import Theorems.Thm_tangent_coordinate_kernel_bound_from_a0_min_dim
import Mathlib.Tactic

open MatrixCompletion

open scoped Classical BigOperators

/-!
Sound `min(n₁,n₂)`-denominator Frobenius bound for the conditional middle base
matrix `quadraticAllDistinctMiddleBaseMatrix` of the triple-decoupled all-distinct
quadratic Neumann term.  Each entry is `G_{ω₂}` (the inner coefficient, bounded
on the inner-coefficient event by `innerBound`) times one tangent-coordinate
kernel `⟪P_T(eᵢeⱼᵀ), e_{w₁}⟫`; the row/column-summed kernel-square is governed by
the diagonal kernel `≤ Cker·μ₀·(r/min)` (A0).

Source: Candès--Recht 2008, PDF p. 31, Lemma 6.8 eq (6.22); rectangular kernel
convention after eqs (6.2)--(6.4).  This is the sound `min`-denominator analogue
of the Disproved max-form supplier; it reuses the kernel-square-sum identity from
the Proved min-dim off-diagonal Frobenius supplier.
-/

namespace MatrixCompletion

private lemma mid_matrixInner_coordinate_right
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

private lemma mid_coordinate_projection_kernel_norm_square
    {N r : ℕ} (u : Fin r → Fin N → ℝ)
    (horth : ∀ k l : Fin r,
      ∑ i : Fin N, u k i * u l i = if k = l then 1 else 0)
    (i : Fin N) :
    ∑ a : Fin N, (∑ k : Fin r, u k a * u k i) ^ 2 =
      ∑ k : Fin r, (u k i) ^ 2 := by
  calc
    ∑ a : Fin N, (∑ k : Fin r, u k a * u k i) ^ 2
        = ∑ a : Fin N, ∑ k : Fin r, ∑ l : Fin r,
            (u k i * u l i) * (u k a * u l a) := by
          apply Finset.sum_congr rfl
          intro a _ha
          simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _hk
          apply Finset.sum_congr rfl
          intro l _hl
          ring
    _ = ∑ k : Fin r, ∑ l : Fin r,
          (u k i * u l i) * (∑ a : Fin N, u k a * u l a) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k _hk
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro l _hl
          rw [Finset.mul_sum]
    _ = ∑ k : Fin r, ∑ l : Fin r,
          (u k i * u l i) * (if k = l then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro k _hk
          apply Finset.sum_congr rfl
          intro l _hl
          rw [horth k l]
    _ = ∑ k : Fin r, (u k i) ^ 2 := by
          apply Finset.sum_congr rfl
          intro k _hk
          rw [Finset.sum_eq_single k]
          · simp [pow_two]
          · intro l _hl hne
            have hkne : k ≠ l := fun h => hne h.symm
            simp [hkne]
          · intro hnot
            exact (hnot (Finset.mem_univ k)).elim

private lemma mid_leftSingularProjection_coordinate_apply
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂)
    (a : Fin n₁) (b : Fin n₂) :
    leftSingularProjection S (coordinateMatrix i j) a b =
      if b = j then ∑ k : Fin r, S.u k a * S.u k i else 0 := by
  unfold leftSingularProjection coordinateMatrix
  by_cases hbj : b = j
  · rw [Finset.sum_eq_single i]
    · simp [hbj]
    · intro x _hx hx
      simp [hx, hbj]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  · rw [Finset.sum_eq_zero]
    · simp [hbj]
    · intro x _hx
      simp [hbj]

private lemma mid_rightSingularProjection_coordinate_apply
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂)
    (a : Fin n₁) (b : Fin n₂) :
    rightSingularProjection S (coordinateMatrix i j) a b =
      if a = i then ∑ k : Fin r, S.v k j * S.v k b else 0 := by
  unfold rightSingularProjection coordinateMatrix
  by_cases hai : a = i
  · rw [Finset.sum_eq_single j]
    · simp [hai]
    · intro x _hx hx
      simp [hai, hx]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  · rw [Finset.sum_eq_zero]
    · simp [hai]
    · intro x _hx
      simp [hai]

private lemma mid_twoSidedSingularProjection_coordinate_apply
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂)
    (a : Fin n₁) (b : Fin n₂) :
    twoSidedSingularProjection S (coordinateMatrix i j) a b =
      (∑ k : Fin r, S.u k a * S.u k i) *
        (∑ k : Fin r, S.v k j * S.v k b) := by
  unfold twoSidedSingularProjection coordinateMatrix
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp [Finset.mul_sum, Finset.sum_mul]
    · intro x _hx hx
      simp [hx]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  · intro x _hx hx
    simp [hx]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private lemma mid_tangentProjection_coordinate_apply
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂)
    (a : Fin n₁) (b : Fin n₂) :
    tangentProjection S (coordinateMatrix i j) a b =
      (if b = j then ∑ k : Fin r, S.u k a * S.u k i else 0) +
        (if a = i then ∑ k : Fin r, S.v k j * S.v k b else 0) -
          (∑ k : Fin r, S.u k a * S.u k i) *
            (∑ k : Fin r, S.v k j * S.v k b) := by
  simp [tangentProjection, mid_leftSingularProjection_coordinate_apply,
    mid_rightSingularProjection_coordinate_apply,
    mid_twoSidedSingularProjection_coordinate_apply]

private lemma mid_tangent_coordinate_kernel_diagonal_formula
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂) :
    tangentCoordinateKernel S i j i j =
      (∑ k : Fin r, (S.u k i) ^ 2) +
        (∑ k : Fin r, (S.v k j) ^ 2) -
          (∑ k : Fin r, (S.u k i) ^ 2) *
            (∑ k : Fin r, (S.v k j) ^ 2) := by
  rw [tangentCoordinateKernel, mid_matrixInner_coordinate_right]
  simp [mid_tangentProjection_coordinate_apply, pow_two]

private lemma mid_tangent_coordinate_kernel_apply_formula
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂)
    (a : Fin n₁) (b : Fin n₂) :
    tangentCoordinateKernel S i j a b =
      (if b = j then ∑ k : Fin r, S.u k a * S.u k i else 0) +
        (if a = i then ∑ k : Fin r, S.v k j * S.v k b else 0) -
          (∑ k : Fin r, S.u k a * S.u k i) *
            (∑ k : Fin r, S.v k j * S.v k b) := by
  rw [tangentCoordinateKernel, mid_matrixInner_coordinate_right]
  exact mid_tangentProjection_coordinate_apply S i j a b

private lemma mid_coordinate_projection_square_sum
    {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (P : α → ℝ) (Q : β → ℝ) (i : α) (j : β)
    (hPi : P i = ∑ a : α, P a ^ 2)
    (hQj : Q j = ∑ b : β, Q b ^ 2) :
    ∑ a : α, ∑ b : β,
      ((if b = j then P a else 0) +
        (if a = i then Q b else 0) - P a * Q b) ^ 2 =
      (∑ a : α, P a ^ 2) +
        (∑ b : β, Q b ^ 2) -
          (∑ a : α, P a ^ 2) * (∑ b : β, Q b ^ 2) := by
  classical
  let A : ℝ := ∑ a : α, P a ^ 2
  let B : ℝ := ∑ b : β, Q b ^ 2
  have hPi' : P i = A := by simpa [A] using hPi
  have hQj' : Q j = B := by simpa [B] using hQj
  have hPQ : (∑ a : α, ∑ b : β, P a ^ 2 * Q b ^ 2) = A * B := by
    dsimp [A, B]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [Finset.mul_sum]
  have hPQsq : (∑ a : α, ∑ b : β, (P a * Q b) ^ 2) = A * B := by
    calc
      ∑ a : α, ∑ b : β, (P a * Q b) ^ 2
          = ∑ a : α, ∑ b : β, P a ^ 2 * Q b ^ 2 := by
            apply Finset.sum_congr rfl
            intro a _ha
            apply Finset.sum_congr rfl
            intro b _hb
            ring
      _ = A * B := hPQ
  have hCrossP : (∑ a : α, 2 * P a * (P a * B)) = 2 * A * B := by
    calc
      ∑ a : α, 2 * P a * (P a * B)
          = ∑ a : α, (2 * B) * P a ^ 2 := by
            apply Finset.sum_congr rfl
            intro a _ha
            ring
      _ = (2 * B) * (∑ a : α, P a ^ 2) := by
            symm
            rw [Finset.mul_sum]
      _ = 2 * A * B := by
            simp [A, mul_assoc, mul_left_comm, mul_comm]
  have hCrossQ : (∑ b : β, 2 * Q b * (A * Q b)) = 2 * A * B := by
    calc
      ∑ b : β, 2 * Q b * (A * Q b)
          = ∑ b : β, (2 * A) * Q b ^ 2 := by
            apply Finset.sum_congr rfl
            intro b _hb
            ring
      _ = (2 * A) * (∑ b : β, Q b ^ 2) := by
            symm
            rw [Finset.mul_sum]
      _ = 2 * A * B := by
            simp [B, mul_assoc]
  calc
    ∑ a : α, ∑ b : β,
      ((if b = j then P a else 0) +
        (if a = i then Q b else 0) - P a * Q b) ^ 2
        = ∑ a : α, ∑ b : β,
            ((if b = j then P a else 0) ^ 2 +
              (if a = i then Q b else 0) ^ 2 +
              (P a * Q b) ^ 2 +
              2 * (if b = j then P a else 0) *
                (if a = i then Q b else 0) -
              2 * (if b = j then P a else 0) * (P a * Q b) -
              2 * (if a = i then Q b else 0) * (P a * Q b)) := by
            apply Finset.sum_congr rfl
            intro a _ha
            apply Finset.sum_congr rfl
            intro b _hb
            ring
    _ = A + B + A * B + 2 * A * B - 2 * A * B - 2 * A * B := by
            simp [hPi', hQj', Finset.sum_add_distrib,
              Finset.sum_sub_distrib]
            rw [hPQsq, hCrossP, hCrossQ]
            ring
    _ = A + B - A * B := by ring
    _ = (∑ a : α, P a ^ 2) +
          (∑ b : β, Q b ^ 2) -
            (∑ a : α, P a ^ 2) * (∑ b : β, Q b ^ 2) := by
            simp [A, B]

private lemma mid_tangent_coordinate_kernel_square_sum_eq_diagonal
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (a : Fin n₁) (b : Fin n₂) :
    ∑ i : Fin n₁, ∑ j : Fin n₂,
        (tangentCoordinateKernel S i j a b) ^ 2 =
      tangentCoordinateKernel S a b a b := by
  let P : Fin n₁ → ℝ := fun i => ∑ k : Fin r, S.u k a * S.u k i
  let Q : Fin n₂ → ℝ := fun j => ∑ k : Fin r, S.v k j * S.v k b
  have hPnorm : ∑ i : Fin n₁, P i ^ 2 = ∑ k : Fin r, (S.u k a) ^ 2 := by
    have hbase :=
      mid_coordinate_projection_kernel_norm_square S.u S.u_orthonormal a
    calc
      ∑ i : Fin n₁, P i ^ 2
          = ∑ i : Fin n₁, (∑ k : Fin r, S.u k i * S.u k a) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _hi
            congr 1
            apply Finset.sum_congr rfl
            intro k _hk
            simp [mul_comm]
      _ = ∑ k : Fin r, (S.u k a) ^ 2 := by
            simpa [pow_two] using hbase
  have hQnorm : ∑ j : Fin n₂, Q j ^ 2 = ∑ k : Fin r, (S.v k b) ^ 2 := by
    have hbase :=
      mid_coordinate_projection_kernel_norm_square S.v S.v_orthonormal b
    simpa [Q, pow_two] using hbase
  have hPa : P a = ∑ k : Fin r, (S.u k a) ^ 2 := by
    simp [P, pow_two]
  have hQb : Q b = ∑ k : Fin r, (S.v k b) ^ 2 := by
    simp [Q, pow_two]
  calc
    ∑ i : Fin n₁, ∑ j : Fin n₂,
        (tangentCoordinateKernel S i j a b) ^ 2
        = ∑ i : Fin n₁, ∑ j : Fin n₂,
            ((if j = b then P i else 0) +
              (if i = a then Q j else 0) - P i * Q j) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _hi
            apply Finset.sum_congr rfl
            intro j _hj
            rw [mid_tangent_coordinate_kernel_apply_formula]
            simp [P, Q, eq_comm]
    _ = (∑ i : Fin n₁, P i ^ 2) +
          (∑ j : Fin n₂, Q j ^ 2) -
            (∑ i : Fin n₁, P i ^ 2) *
              (∑ j : Fin n₂, Q j ^ 2) := by
            exact mid_coordinate_projection_square_sum P Q a b
              (hPa.trans hPnorm.symm) (hQb.trans hQnorm.symm)
    _ = (∑ k : Fin r, (S.u k a) ^ 2) +
          (∑ k : Fin r, (S.v k b) ^ 2) -
            (∑ k : Fin r, (S.u k a) ^ 2) *
              (∑ k : Fin r, (S.v k b) ^ 2) := by
            rw [hPnorm, hQnorm]
    _ = tangentCoordinateKernel S a b a b := by
            rw [mid_tangent_coordinate_kernel_diagonal_formula]

/-- Frobenius-square bound for the middle base matrix: each entry is bounded by
`innerBound · |kernel|`, so the Frobenius square is `≤ innerBound² · Σ kernel²`. -/
private lemma mid_frobeniusNormSq_base_le
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega3 : Finset (Fin n₁ × Fin n₂)) (p innerBound : ℝ)
    (hib : 0 ≤ innerBound)
    (hInner : QuadraticAllDistinctInnerCoefficientBound Omega3 S p innerBound)
    (w1 : Fin n₁ × Fin n₂) :
    frobeniusNormSq (quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1) ≤
      innerBound ^ 2 *
        (∑ i : Fin n₁, ∑ j : Fin n₂,
          (tangentCoordinateKernel S i j w1.1 w1.2) ^ 2) := by
  unfold frobeniusNormSq
  calc
    ∑ i : Fin n₁, ∑ j : Fin n₂,
        (quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1 i j) ^ 2
        ≤ ∑ i : Fin n₁, ∑ j : Fin n₂,
            innerBound ^ 2 * (tangentCoordinateKernel S i j w1.1 w1.2) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _hi
          apply Finset.sum_le_sum
          intro j _hj
          by_cases hsame : (i, j) = w1
          · simp [quadraticAllDistinctMiddleBaseMatrix, hsame]
            positivity
          · have hcoeff :
                |quadraticAllDistinctInnerCoefficient Omega3 S p w1 (i, j)| ≤
                  innerBound := hInner w1 (i, j)
            have hcoeffsq :
                (quadraticAllDistinctInnerCoefficient Omega3 S p w1 (i, j)) ^ 2 ≤
                  innerBound ^ 2 := by
              have := sq_le_sq' (neg_le_of_abs_le hcoeff) (le_of_abs_le hcoeff)
              simpa using this
            have hmul :=
              mul_le_mul_of_nonneg_right hcoeffsq
                (sq_nonneg (tangentCoordinateKernel S i j w1.1 w1.2))
            simpa [quadraticAllDistinctMiddleBaseMatrix, hsame, pow_two,
              mul_assoc, mul_left_comm, mul_comm] using hmul
    _ = innerBound ^ 2 *
        (∑ i : Fin n₁, ∑ j : Fin n₂,
          (tangentCoordinateKernel S i j w1.1 w1.2) ^ 2) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.mul_sum]

end MatrixCompletion

open MatrixCompletion

/-- Source: Candès--Recht 2008, PDF p. 31, Lemma 6.8 eq (6.22); rectangular
`min(n₁,n₂)` kernel convention after eqs (6.2)--(6.4). -/
theorem solution :
    ∃ Cfro : ℝ, 0 < Cfro ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        ∀ (Omega3 : Finset (Fin n₁ × Fin n₂)) (p innerBound : ℝ),
        0 ≤ innerBound →
        QuadraticAllDistinctInnerCoefficientBound Omega3 S p innerBound →
        ∀ w1 : Fin n₁ × Fin n₂,
          frobeniusNorm
              (quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1) ≤
            Cfro * innerBound *
              Real.sqrt (μ₀ * ((r : ℝ) / (↑(min n₁ n₂)))) := by
  rcases tangent_coordinate_kernel_bound_from_a0_min_dim with
    ⟨Cker, hCker_pos, hKernel⟩
  refine ⟨Real.sqrt Cker, Real.sqrt_pos.2 hCker_pos, ?_⟩
  intro n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 Omega3 p innerBound hib hInner w1
  set kernelScale : ℝ := μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) with hkernelScale
  have hKernelScale_nonneg : 0 ≤ kernelScale := by
    rw [hkernelScale]; positivity
  have hCker_nonneg : 0 ≤ Cker := le_of_lt hCker_pos
  have hsqBase :=
    mid_frobeniusNormSq_base_le S Omega3 p innerBound hib hInner w1
  have hKernelSq :
      (∑ i : Fin n₁, ∑ j : Fin n₂,
          (tangentCoordinateKernel S i j w1.1 w1.2) ^ 2) ≤
        Cker * kernelScale := by
    have hsum :=
      mid_tangent_coordinate_kernel_square_sum_eq_diagonal S w1.1 w1.2
    have hdiag :=
      hKernel n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 w1.1 w1.2 w1.1 w1.2
    calc
      ∑ i : Fin n₁, ∑ j : Fin n₂,
          (tangentCoordinateKernel S i j w1.1 w1.2) ^ 2
          = tangentCoordinateKernel S w1.1 w1.2 w1.1 w1.2 := hsum
      _ ≤ |tangentCoordinateKernel S w1.1 w1.2 w1.1 w1.2| := le_abs_self _
      _ ≤ Cker * kernelScale := by
          simpa [hkernelScale, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
            using hdiag
  have hsq :
      frobeniusNormSq (quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1) ≤
        innerBound ^ 2 * (Cker * kernelScale) := by
    exact le_trans hsqBase
      (mul_le_mul_of_nonneg_left hKernelSq (sq_nonneg innerBound))
  have hsqrt :
      frobeniusNorm (quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1) ≤
        Real.sqrt (innerBound ^ 2 * (Cker * kernelScale)) := by
    unfold frobeniusNorm
    exact Real.sqrt_le_sqrt hsq
  have hsqrt_eq :
      Real.sqrt (innerBound ^ 2 * (Cker * kernelScale)) =
        Real.sqrt Cker * innerBound * Real.sqrt kernelScale := by
    rw [Real.sqrt_mul (sq_nonneg innerBound)]
    rw [Real.sqrt_sq_eq_abs]
    rw [abs_of_nonneg hib]
    rw [Real.sqrt_mul hCker_nonneg]
    ring
  calc
    frobeniusNorm (quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1)
        ≤ Real.sqrt (innerBound ^ 2 * (Cker * kernelScale)) := hsqrt
    _ = Real.sqrt Cker * innerBound * Real.sqrt kernelScale := hsqrt_eq
    _ = Real.sqrt Cker * innerBound *
          Real.sqrt (μ₀ * ((r : ℝ) / (↑(min n₁ n₂)))) := by
          rw [hkernelScale]
