-- Prove2me | solution 1 for quadratic_neumann_first_index_distinct_centered_base_frobenius_norm_bound_min_dim
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-01T09:18:03.216051+00:00
-- url     : https://prove2.me/submissions/b44586e4-b62e-45ab-a1d1-f8e638e03748

import Theorems.Thm_tangent_coordinate_kernel_bound_from_a0_min_dim
import Mathlib.Tactic

open MatrixCompletion

open scoped Classical BigOperators

/-!
# Per-entry FROBENIUS base bound for the first-index centered coefficient (min-dim)

Source: Candès--Recht 2008, §6.3, PDF pp. 31--32, the two-copy decoupled
`ω₁ ≠ ω₂ = ω₃` centered quadratic term (Lemma 6.7), applied with
`X_ω = p^{-1} E_ω P_{ωω}` (the diagonal-weighted sign matrix
`linearNeumannDiagonalBaseMatrix S`).

The output coordinate `(i,j)` of the conditional coefficient matrix
`quadraticFirstIndexDistinctCenteredCoefficientMatrix Ω2 S p` is the scalar
centered sampling fluctuation of the fixed matrix

  `B^{(ij)}_{ab} = if (a,b) = (i,j) then 0
                   else (E_{ab} · ⟪P_T e_{ab}, e_{ab}⟫) · ⟪P_T e_{ab}, e_{ij}⟫`
              = if (a,b) = (i,j) then 0
                   else (linearNeumannDiagonalBaseMatrix S a b) · K(a,b,i,j).

This node bounds the Frobenius norm of that fixed base.  Its scale carries the
`min(n₁,n₂)` rectangular denominator and, compared with the off-diagonal base
`E_{ab}·K(a,b,i,j)` (Frobenius bound
`Cfro·μ₁·√(r/(n₁n₂))·√(μ₀r/min)`), an EXTRA diagonal-kernel factor
`Cker·μ₀·r/min` coming from replacing the sign `E_{ab}` by the diagonal-weighted
`E_{ab}·K(a,b,a,b)`.

The Frobenius identity `∑_{ab} K(a,b,i,j)² = K(i,j,i,j)` (an orthonormality
computation of the tangent projection) is inlined here, then combined with the
A1 sign bound `|E| ≤ μ₁√(r/(n₁n₂))`, the A0 diagonal-kernel bound
`|K(ab,ab)| ≤ Cker μ₀ r/min`, and `K(i,j,i,j) ≤ Cker μ₀ r/min`.
-/

namespace MatrixCompletion

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

private lemma coordinate_projection_kernel_norm_square
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

private lemma leftSingularProjection_coordinate_apply
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

private lemma rightSingularProjection_coordinate_apply
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

private lemma twoSidedSingularProjection_coordinate_apply
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

private lemma tangentProjection_coordinate_apply
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂)
    (a : Fin n₁) (b : Fin n₂) :
    tangentProjection S (coordinateMatrix i j) a b =
      (if b = j then ∑ k : Fin r, S.u k a * S.u k i else 0) +
        (if a = i then ∑ k : Fin r, S.v k j * S.v k b else 0) -
          (∑ k : Fin r, S.u k a * S.u k i) *
            (∑ k : Fin r, S.v k j * S.v k b) := by
  simp [tangentProjection, leftSingularProjection_coordinate_apply,
    rightSingularProjection_coordinate_apply,
    twoSidedSingularProjection_coordinate_apply]

private lemma tangent_coordinate_kernel_diagonal_formula
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂) :
    tangentCoordinateKernel S i j i j =
      (∑ k : Fin r, (S.u k i) ^ 2) +
        (∑ k : Fin r, (S.v k j) ^ 2) -
          (∑ k : Fin r, (S.u k i) ^ 2) *
            (∑ k : Fin r, (S.v k j) ^ 2) := by
  rw [tangentCoordinateKernel, matrixInner_coordinate_right]
  simp [tangentProjection_coordinate_apply, pow_two]

private lemma tangent_coordinate_kernel_apply_formula
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂)
    (a : Fin n₁) (b : Fin n₂) :
    tangentCoordinateKernel S i j a b =
      (if b = j then ∑ k : Fin r, S.u k a * S.u k i else 0) +
        (if a = i then ∑ k : Fin r, S.v k j * S.v k b else 0) -
          (∑ k : Fin r, S.u k a * S.u k i) *
            (∑ k : Fin r, S.v k j * S.v k b) := by
  rw [tangentCoordinateKernel, matrixInner_coordinate_right]
  exact tangentProjection_coordinate_apply S i j a b

private lemma coordinate_projection_square_sum
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

/-- `∑_{ab} K(a,b,i,j)² = K(i,j,i,j)` for the tangent-coordinate kernel. -/
private lemma tangent_coordinate_kernel_square_sum_eq_diagonal
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (a : Fin n₁) (b : Fin n₂) :
    ∑ i : Fin n₁, ∑ j : Fin n₂,
        (tangentCoordinateKernel S i j a b) ^ 2 =
      tangentCoordinateKernel S a b a b := by
  let P : Fin n₁ → ℝ := fun i => ∑ k : Fin r, S.u k a * S.u k i
  let Q : Fin n₂ → ℝ := fun j => ∑ k : Fin r, S.v k j * S.v k b
  have hPnorm : ∑ i : Fin n₁, P i ^ 2 = ∑ k : Fin r, (S.u k a) ^ 2 := by
    have hbase :=
      coordinate_projection_kernel_norm_square S.u S.u_orthonormal a
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
      coordinate_projection_kernel_norm_square S.v S.v_orthonormal b
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
            rw [tangent_coordinate_kernel_apply_formula]
            simp [P, Q, eq_comm]
    _ = (∑ i : Fin n₁, P i ^ 2) +
          (∑ j : Fin n₂, Q j ^ 2) -
            (∑ i : Fin n₁, P i ^ 2) *
              (∑ j : Fin n₂, Q j ^ 2) := by
            exact coordinate_projection_square_sum P Q a b
              (hPa.trans hPnorm.symm) (hQb.trans hQnorm.symm)
    _ = (∑ k : Fin r, (S.u k a) ^ 2) +
          (∑ k : Fin r, (S.v k b) ^ 2) -
            (∑ k : Fin r, (S.u k a) ^ 2) *
              (∑ k : Fin r, (S.v k b) ^ 2) := by
            rw [hPnorm, hQnorm]
    _ = tangentCoordinateKernel S a b a b := by
            rw [tangent_coordinate_kernel_diagonal_formula]

end MatrixCompletion

/-- Per-entry Frobenius base bound for the first-index centered coefficient.

For output coordinate `w = (i,j)`, the fixed base matrix
`B^{(w)}_{ab} = if (a,b) = w then 0
               else (linearNeumannDiagonalBaseMatrix S a b) · K(a,b,w.1,w.2)`
has Frobenius norm bounded (min-dim, `μ₁`-explicit) by

  `Cfro · μ₁ · √(r/(n₁n₂)) · √(μ₀r/min) · (μ₀r/min)`.

The extra factor `(μ₀r/min)` relative to the off-diagonal base is the
diagonal-kernel weight `K(ab,ab)`. -/
theorem solution :
    ∃ Cfro : ℝ, 0 < Cfro ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        ∀ w : Fin n₁ × Fin n₂,
          frobeniusNorm
              (fun a b =>
                if (a, b) = w then 0
                else
                  linearNeumannDiagonalBaseMatrix S a b *
                    tangentCoordinateKernel S a b w.1 w.2) ≤
            Cfro * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                  (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
  rcases tangent_coordinate_kernel_bound_from_a0_min_dim with
    ⟨Cker, hCker_pos, hKernel⟩
  refine ⟨Real.sqrt Cker * Cker, by positivity, ?_⟩
  intro n₁ n₂ r M μ₀ μ₁ S hn₁ hn₂ hr hμ₀ hμ₁ hA0 hA1 w
  set signScale : ℝ := μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
    with hsignScale
  set kernelScale : ℝ := μ₀ * (r : ℝ) / (↑(min n₁ n₂)) with hkernelScale
  have hSignScale_nonneg : 0 ≤ signScale := by rw [hsignScale]; positivity
  have hKernelScale_nonneg : 0 ≤ kernelScale := by rw [hkernelScale]; positivity
  have hCker_nonneg : 0 ≤ Cker := le_of_lt hCker_pos
  -- diagonal-weighted sign bound: |linearNeumannDiagonalBaseMatrix S a b| ≤ signScale · Cker·kernelScale
  have hDiagBase : ∀ a b,
      |linearNeumannDiagonalBaseMatrix S a b| ≤ signScale * (Cker * kernelScale) := by
    intro a b
    have hEab : |signMatrix S a b| ≤ signScale := by
      rw [hsignScale]; exact hA1 a b
    have hKab : |tangentCoordinateKernel S a b a b| ≤ Cker * kernelScale := by
      rw [hkernelScale]
      have := hKernel n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 a b a b
      simpa [mul_assoc, div_eq_mul_inv] using this
    have hBaseEq : linearNeumannDiagonalBaseMatrix S a b =
        signMatrix S a b * tangentCoordinateKernel S a b a b := rfl
    rw [hBaseEq, abs_mul]
    exact mul_le_mul hEab hKab (abs_nonneg _) hSignScale_nonneg
  -- Frobenius square bound
  have hDiagBase_nonneg : 0 ≤ signScale * (Cker * kernelScale) := by positivity
  have hsqBase :
      frobeniusNormSq
          (fun a b =>
            if (a, b) = w then 0
            else
              linearNeumannDiagonalBaseMatrix S a b *
                tangentCoordinateKernel S a b w.1 w.2) ≤
        (signScale * (Cker * kernelScale)) ^ 2 *
          (∑ a : Fin n₁, ∑ b : Fin n₂,
            (tangentCoordinateKernel S a b w.1 w.2) ^ 2) := by
    unfold frobeniusNormSq
    calc
      ∑ a : Fin n₁, ∑ b : Fin n₂,
          (if (a, b) = w then 0
            else
              linearNeumannDiagonalBaseMatrix S a b *
                tangentCoordinateKernel S a b w.1 w.2) ^ 2
          ≤ ∑ a : Fin n₁, ∑ b : Fin n₂,
              (signScale * (Cker * kernelScale)) ^ 2 *
                (tangentCoordinateKernel S a b w.1 w.2) ^ 2 := by
            apply Finset.sum_le_sum
            intro a _ha
            apply Finset.sum_le_sum
            intro b _hb
            by_cases hsame : (a, b) = w
            · rw [if_pos hsame]
              have h0 : (0 : ℝ) ^ 2 = 0 := by norm_num
              rw [h0]
              positivity
            · rw [if_neg hsame]
              have hbaseSq :
                  (linearNeumannDiagonalBaseMatrix S a b) ^ 2 ≤
                    (signScale * (Cker * kernelScale)) ^ 2 := by
                have hbnd := hDiagBase a b
                calc (linearNeumannDiagonalBaseMatrix S a b) ^ 2
                    = |linearNeumannDiagonalBaseMatrix S a b| ^ 2 := by rw [sq_abs]
                  _ ≤ (signScale * (Cker * kernelScale)) ^ 2 :=
                      pow_le_pow_left₀ (abs_nonneg _) hbnd 2
              have hmul :=
                mul_le_mul_of_nonneg_right hbaseSq
                  (sq_nonneg (tangentCoordinateKernel S a b w.1 w.2))
              calc
                (linearNeumannDiagonalBaseMatrix S a b *
                    tangentCoordinateKernel S a b w.1 w.2) ^ 2
                    = (linearNeumannDiagonalBaseMatrix S a b) ^ 2 *
                        (tangentCoordinateKernel S a b w.1 w.2) ^ 2 := by ring
                  _ ≤ (signScale * (Cker * kernelScale)) ^ 2 *
                        (tangentCoordinateKernel S a b w.1 w.2) ^ 2 := hmul
      _ = (signScale * (Cker * kernelScale)) ^ 2 *
            (∑ a : Fin n₁, ∑ b : Fin n₂,
              (tangentCoordinateKernel S a b w.1 w.2) ^ 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _ha
            rw [Finset.mul_sum]
  -- kernel sum ≤ Cker·kernelScale
  have hKernelSq :
      (∑ a : Fin n₁, ∑ b : Fin n₂,
          (tangentCoordinateKernel S a b w.1 w.2) ^ 2) ≤
        Cker * kernelScale := by
    have hsum := tangent_coordinate_kernel_square_sum_eq_diagonal S w.1 w.2
    have hdiag := hKernel n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 w.1 w.2 w.1 w.2
    calc
      ∑ a : Fin n₁, ∑ b : Fin n₂,
          (tangentCoordinateKernel S a b w.1 w.2) ^ 2
          = tangentCoordinateKernel S w.1 w.2 w.1 w.2 := hsum
      _ ≤ |tangentCoordinateKernel S w.1 w.2 w.1 w.2| := le_abs_self _
      _ ≤ Cker * kernelScale := by
          rw [hkernelScale]
          simpa [mul_assoc, div_eq_mul_inv] using hdiag
  -- combine
  have hsq :
      frobeniusNormSq
          (fun a b =>
            if (a, b) = w then 0
            else
              linearNeumannDiagonalBaseMatrix S a b *
                tangentCoordinateKernel S a b w.1 w.2) ≤
        (signScale * (Cker * kernelScale)) ^ 2 * (Cker * kernelScale) := by
    refine le_trans hsqBase ?_
    exact mul_le_mul_of_nonneg_left hKernelSq (sq_nonneg _)
  have hsqrt :
      frobeniusNorm
          (fun a b =>
            if (a, b) = w then 0
            else
              linearNeumannDiagonalBaseMatrix S a b *
                tangentCoordinateKernel S a b w.1 w.2) ≤
        Real.sqrt ((signScale * (Cker * kernelScale)) ^ 2 * (Cker * kernelScale)) := by
    unfold frobeniusNorm
    exact Real.sqrt_le_sqrt hsq
  have hsqrt_eq :
      Real.sqrt ((signScale * (Cker * kernelScale)) ^ 2 * (Cker * kernelScale)) =
        (signScale * (Cker * kernelScale)) * Real.sqrt (Cker * kernelScale) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
      abs_of_nonneg hDiagBase_nonneg]
  refine le_trans hsqrt (le_of_eq ?_)
  rw [hsqrt_eq]
  -- (signScale·Cker·kernelScale)·√(Cker·kernelScale)
  --   = (√Cker·Cker) · μ₁ · √(r/(n₁n₂)) · √kernelScale · kernelScale
  have hsqrtCkerKS : Real.sqrt (Cker * kernelScale) =
      Real.sqrt Cker * Real.sqrt kernelScale := Real.sqrt_mul hCker_nonneg _
  rw [hsqrtCkerKS, hsignScale]
  ring
