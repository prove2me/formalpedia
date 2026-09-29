-- Prove2me | solution 1 for tangent_coordinate_kernel_bound_from_a0_min_dim
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-30T10:39:52.626255+00:00
-- url     : https://prove2.me/submissions/efb1c609-304d-44a8-9852-d3ccb0754f1d

import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_a0_singular_coordinate_energy_bounds
import Theorems.Thm_svd_singular_coordinate_energy_le_one
import Mathlib.Tactic

open MatrixCompletion
open scoped Classical BigOperators

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

private lemma abs_cross_sum_le_sqrt_mul_sqrt
    {N r : ℕ} (u : Fin r → Fin N → ℝ) (i a : Fin N) :
    |∑ k : Fin r, u k i * u k a| ≤
      Real.sqrt (∑ k : Fin r, (u k i) ^ 2) *
        Real.sqrt (∑ k : Fin r, (u k a) ^ 2) := by
  calc
    |∑ k : Fin r, u k i * u k a|
        ≤ ∑ k : Fin r, |u k i * u k a| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin r, |u k i| * |u k a| := by
      simp [abs_mul]
    _ ≤ Real.sqrt (∑ k : Fin r, |u k i| ^ 2) *
          Real.sqrt (∑ k : Fin r, |u k a| ^ 2) := by
      simpa using
        (Real.sum_mul_le_sqrt_mul_sqrt
          (Finset.univ : Finset (Fin r))
          (fun k => |u k i|) (fun k => |u k a|))
    _ = Real.sqrt (∑ k : Fin r, (u k i) ^ 2) *
          Real.sqrt (∑ k : Fin r, (u k a) ^ 2) := by
      simp [sq_abs]

private lemma cross_sum_abs_le_scale_same_dim
    {N r : ℕ} (hN : 0 < N) (hr : 0 < r)
    (u : Fin r → Fin N → ℝ) {μ : ℝ} (hμ : 1 ≤ μ)
    (hEnergy : ∀ i : Fin N, ∑ k : Fin r, (u k i) ^ 2 ≤ μ * (r : ℝ) / (N : ℝ)) :
    ∀ i a : Fin N,
      |∑ k : Fin r, u k i * u k a| ≤ μ * (r : ℝ) / (N : ℝ) := by
  intro i a
  have hscale_nonneg : 0 ≤ μ * (r : ℝ) / (N : ℝ) := by positivity
  calc
    |∑ k : Fin r, u k i * u k a|
        ≤ Real.sqrt (∑ k : Fin r, (u k i) ^ 2) *
          Real.sqrt (∑ k : Fin r, (u k a) ^ 2) :=
          abs_cross_sum_le_sqrt_mul_sqrt u i a
    _ ≤ Real.sqrt (μ * (r : ℝ) / (N : ℝ)) *
          Real.sqrt (μ * (r : ℝ) / (N : ℝ)) := by
      exact mul_le_mul (Real.sqrt_le_sqrt (hEnergy i))
        (Real.sqrt_le_sqrt (hEnergy a)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = μ * (r : ℝ) / (N : ℝ) := by
      rw [← sq]
      exact Real.sq_sqrt hscale_nonneg

private lemma cross_sum_abs_le_one
    {N r : ℕ} (u : Fin r → Fin N → ℝ)
    (hOne : ∀ i : Fin N, ∑ k : Fin r, (u k i) ^ 2 ≤ (1 : ℝ)) :
    ∀ i a : Fin N,
      |∑ k : Fin r, u k i * u k a| ≤ (1 : ℝ) := by
  intro i a
  calc
    |∑ k : Fin r, u k i * u k a|
        ≤ Real.sqrt (∑ k : Fin r, (u k i) ^ 2) *
          Real.sqrt (∑ k : Fin r, (u k a) ^ 2) :=
          abs_cross_sum_le_sqrt_mul_sqrt u i a
    _ ≤ Real.sqrt (1 : ℝ) * Real.sqrt (1 : ℝ) := by
      exact mul_le_mul (Real.sqrt_le_sqrt (hOne i))
        (Real.sqrt_le_sqrt (hOne a)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = 1 := by norm_num

private lemma same_dim_scale_le_min_scale
    {n₁ n₂ r : ℕ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hr : 0 < r) {μ₀ : ℝ} (hμ₀ : 1 ≤ μ₀) :
    μ₀ * (r : ℝ) / (n₁ : ℝ) ≤
      μ₀ * (r : ℝ) / (((min n₁ n₂ : ℕ) : ℝ)) ∧
    μ₀ * (r : ℝ) / (n₂ : ℝ) ≤
      μ₀ * (r : ℝ) / (((min n₁ n₂ : ℕ) : ℝ)) := by
  have hA_nonneg : 0 ≤ μ₀ * (r : ℝ) := by positivity
  constructor
  · have hmin_le : (((min n₁ n₂ : ℕ) : ℝ)) ≤ (n₁ : ℝ) := by
      exact_mod_cast min_le_left n₁ n₂
    gcongr
  · have hmin_le : (((min n₁ n₂ : ℕ) : ℝ)) ≤ (n₂ : ℝ) := by
      exact_mod_cast min_le_right n₁ n₂
    gcongr

private lemma tangent_coordinate_kernel_formula
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂) (a : Fin n₁) (b : Fin n₂) :
    tangentCoordinateKernel S i j a b =
      (if j = b then ∑ k : Fin r, S.u k i * S.u k a else 0) +
        (if i = a then ∑ k : Fin r, S.v k j * S.v k b else 0) -
          (∑ k : Fin r, S.u k i * S.u k a) *
            (∑ k : Fin r, S.v k j * S.v k b) := by
  rw [tangentCoordinateKernel, matrixInner_coordinate_right]
  have hleft :
      leftSingularProjection S (coordinateMatrix i j) a b =
        if j = b then ∑ k : Fin r, S.u k i * S.u k a else 0 := by
    unfold leftSingularProjection coordinateMatrix
    by_cases hbj : b = j
    · rw [Finset.sum_eq_single i]
      · simp [hbj, mul_comm]
      · intro x _hx hx
        simp [hx, hbj]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    · rw [Finset.sum_eq_zero]
      · have hjb : ¬ j = b := fun h => hbj h.symm
        simp [hjb]
      · intro x _hx
        simp [hbj]
  have hright :
      rightSingularProjection S (coordinateMatrix i j) a b =
        if i = a then ∑ k : Fin r, S.v k j * S.v k b else 0 := by
    unfold rightSingularProjection coordinateMatrix
    by_cases hai : a = i
    · rw [Finset.sum_eq_single j]
      · simp [hai]
      · intro y _hy hy
        simp [hai, hy]
      · intro hj
        exact (hj (Finset.mem_univ j)).elim
    · rw [Finset.sum_eq_zero]
      · have hia : ¬ i = a := fun h => hai h.symm
        simp [hia]
      · intro y _hy
        simp [hai]
  have htwo :
      twoSidedSingularProjection S (coordinateMatrix i j) a b =
        (∑ k : Fin r, S.u k i * S.u k a) *
          (∑ k : Fin r, S.v k j * S.v k b) := by
    unfold twoSidedSingularProjection coordinateMatrix
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · simp [Finset.mul_sum, mul_comm, mul_assoc]
      · intro y _hy hy
        simp [hy]
      · intro hj
        exact (hj (Finset.mem_univ j)).elim
    · intro x _hx hx
      simp [hx]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  simp [tangentProjection, hleft, hright, htwo]

/-- Source: Candes--Recht 2008, PDF p. 23, equation (6.2), together with the
rectangular convention stated immediately after equations (6.2)--(6.4).

The proof expands `P_T(e_i e_j^*)`, bounds the left and right singular-vector
cross terms by Cauchy--Schwarz from A0 and Bessel, and absorbs `n₁`/`n₂` into
`min(n₁,n₂)`. -/
theorem solution :
    ∃ Cker : ℝ, 0 < Cker ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        ∀ i j a b,
          |tangentCoordinateKernel S i j a b| ≤
            Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by
  refine ⟨3, by norm_num, ?_⟩
  intro n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 i j a b
  have hEnergy := a0_singular_coordinate_energy_bounds S μ₀ hn₁ hn₂ hr hA0
  have hOne := svd_singular_coordinate_energy_le_one S
  let scale : ℝ := μ₀ * (r : ℝ) / (((min n₁ n₂ : ℕ) : ℝ))
  have hscale_nonneg : 0 ≤ scale := by
    dsimp [scale]
    positivity
  have hleft_raw :
      |∑ k : Fin r, S.u k i * S.u k a| ≤ μ₀ * (r : ℝ) / (n₁ : ℝ) :=
    cross_sum_abs_le_scale_same_dim hn₁ hr S.u hμ₀ hEnergy.1 i a
  have hright_raw :
      |∑ k : Fin r, S.v k j * S.v k b| ≤ μ₀ * (r : ℝ) / (n₂ : ℝ) :=
    cross_sum_abs_le_scale_same_dim hn₂ hr S.v hμ₀ hEnergy.2 j b
  have hscale_le := same_dim_scale_le_min_scale hn₁ hn₂ hr hμ₀
  have hleft : |∑ k : Fin r, S.u k i * S.u k a| ≤ scale := by
    exact le_trans hleft_raw hscale_le.1
  have hright : |∑ k : Fin r, S.v k j * S.v k b| ≤ scale := by
    exact le_trans hright_raw hscale_le.2
  have hleft_one : |∑ k : Fin r, S.u k i * S.u k a| ≤ (1 : ℝ) :=
    cross_sum_abs_le_one S.u hOne.1 i a
  have hright_one : |∑ k : Fin r, S.v k j * S.v k b| ≤ (1 : ℝ) :=
    cross_sum_abs_le_one S.v hOne.2 j b
  have hprod :
      |(∑ k : Fin r, S.u k i * S.u k a) *
          (∑ k : Fin r, S.v k j * S.v k b)| ≤ scale := by
    rw [abs_mul]
    calc
      |∑ k : Fin r, S.u k i * S.u k a| *
          |∑ k : Fin r, S.v k j * S.v k b|
          ≤ 1 * scale := by
            exact mul_le_mul hleft_one hright (abs_nonneg _) zero_le_one
      _ = scale := by ring
  have hterm_left :
      |(if j = b then ∑ k : Fin r, S.u k i * S.u k a else 0)| ≤ scale := by
    by_cases h : j = b
    · simpa [h] using hleft
    · simp [h, hscale_nonneg]
  have hterm_right :
      |(if i = a then ∑ k : Fin r, S.v k j * S.v k b else 0)| ≤ scale := by
    by_cases h : i = a
    · simpa [h] using hright
    · simp [h, hscale_nonneg]
  have hformula := tangent_coordinate_kernel_formula S i j a b
  calc
    |tangentCoordinateKernel S i j a b|
        = |(if j = b then ∑ k : Fin r, S.u k i * S.u k a else 0) +
            (if i = a then ∑ k : Fin r, S.v k j * S.v k b else 0) -
              (∑ k : Fin r, S.u k i * S.u k a) *
                (∑ k : Fin r, S.v k j * S.v k b)| := by
          rw [hformula]
    _ ≤ |(if j = b then ∑ k : Fin r, S.u k i * S.u k a else 0)| +
          |(if i = a then ∑ k : Fin r, S.v k j * S.v k b else 0)| +
            |(∑ k : Fin r, S.u k i * S.u k a) *
              (∑ k : Fin r, S.v k j * S.v k b)| := by
          have hsub :
              |((if j = b then ∑ k : Fin r, S.u k i * S.u k a else 0) +
                  (if i = a then ∑ k : Fin r, S.v k j * S.v k b else 0)) -
                  (∑ k : Fin r, S.u k i * S.u k a) *
                    (∑ k : Fin r, S.v k j * S.v k b)| ≤
                |(if j = b then ∑ k : Fin r, S.u k i * S.u k a else 0) +
                  (if i = a then ∑ k : Fin r, S.v k j * S.v k b else 0)| +
                  |(∑ k : Fin r, S.u k i * S.u k a) *
                    (∑ k : Fin r, S.v k j * S.v k b)| := by
            have h :=
              abs_add_le
                ((if j = b then ∑ k : Fin r, S.u k i * S.u k a else 0) +
                  (if i = a then ∑ k : Fin r, S.v k j * S.v k b else 0))
                (-((∑ k : Fin r, S.u k i * S.u k a) *
                    (∑ k : Fin r, S.v k j * S.v k b)))
            simpa [sub_eq_add_neg, abs_neg] using h
          have hsum :=
            abs_add_le (if j = b then ∑ k : Fin r, S.u k i * S.u k a else 0)
              (if i = a then ∑ k : Fin r, S.v k j * S.v k b else 0)
          linarith
    _ ≤ scale + scale + scale := by
          linarith
    _ = 3 * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by
          dsimp [scale]
          ring
