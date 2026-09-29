-- Prove2me | solution 1 for linear_neumann_diagonal_centered_threshold_from_centered_sampling_bound
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T13:59:09.267734+00:00
-- url     : https://prove2.me/submissions/75c1e5bd-4fe8-4bcd-b9c6-8f867aea280f

import Definitions.Def_matrix_completion_svd
import Mathlib
import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_neumann

/- Complete locally authored component: SvdLeverage.lean; SHA256 d0afce6765032f7a3970d12f85ee70eb24ab340c4342e5b77b7cae363bae3546. -/

namespace MatrixThreshold

open MatrixCompletion
open scoped BigOperators

theorem sum_sq_orthonormal_combination {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] (c : I -> Real) (v : I -> J -> Real)
    (hv : ∀ k l, ∑ j, v k j * v l j = if k = l then 1 else 0) :
    ∑ j, (∑ k, c k * v k j) ^ 2 = ∑ k, c k ^ 2 := by
  classical
  calc
    _ = ∑ k, ∑ l, c k * c l * (∑ j, v k j * v l j) := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro j hj
      all_goals first | rfl | ring | field_simp
    _ = _ := by simp [hv, pow_two]

theorem orthonormal_leverage_le_one {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] (v : I -> J -> Real)
    (hv : ∀ k l, ∑ j, v k j * v l j = if k = l then 1 else 0) (i : J) :
    ∑ k, (v k i) ^ 2 <= 1 := by
  classical
  have h := sum_sq_orthonormal_combination (fun k => v k i) v hv
  have hle := Finset.single_le_sum
    (fun j (_ : j ∈ Finset.univ) => sq_nonneg (∑ k, v k i * v k j))
    (Finset.mem_univ i)
  rw [h] at hle
  simp only [← pow_two] at hle
  nlinarith [sq_nonneg ((∑ k, (v k i) ^ 2) - 1)]

theorem sign_row_sq_sum_eq_leverage {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (i : Fin n1) :
    ∑ j, (signMatrix S i j) ^ 2 = ∑ k, (S.u k i) ^ 2 := by
  simpa [signMatrix, Matrix.sum_apply, Matrix.vecMulVec_apply] using
    sum_sq_orthonormal_combination (fun k => S.u k i) S.v S.v_orthonormal

theorem sign_column_sq_sum_eq_leverage {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (j : Fin n2) :
    ∑ i, (signMatrix S i j) ^ 2 = ∑ k, (S.v k j) ^ 2 := by
  simpa [signMatrix, Matrix.sum_apply, Matrix.vecMulVec_apply, mul_comm] using
    sum_sq_orthonormal_combination (fun k => S.v k j) S.u S.u_orthonormal

theorem row_leverage_le_one {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (i : Fin n1) : ∑ k, (S.u k i) ^ 2 <= 1 :=
  orthonormal_leverage_le_one S.u S.u_orthonormal i

theorem column_leverage_le_one {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (j : Fin n2) : ∑ k, (S.v k j) ^ 2 <= 1 :=
  orthonormal_leverage_le_one S.v S.v_orthonormal j

theorem sign_sq_le_of_A1 {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (mu : Real) (hmu : 0 <= mu) (hA1 : A1 S mu)
    (i : Fin n1) (j : Fin n2) :
    (signMatrix S i j) ^ 2 <= mu ^ 2 * (r : Real) / ((n1 : Real) * (n2 : Real)) := by
  have h := sq_le_sq₀ (abs_nonneg (signMatrix S i j))
    (mul_nonneg hmu (Real.sqrt_nonneg ((r : Real) / ((n1 : Real) * (n2 : Real)))))
  have hs := h.mpr (hA1 i j)
  rw [sq_abs, mul_pow, Real.sq_sqrt (by positivity)] at hs
  convert hs using 1
  all_goals first | rfl | ring | field_simp

theorem row_leverage_le_of_A1 {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (mu : Real) (hn1 : 0 < n1) (hn2 : 0 < n2)
    (hmu : 0 <= mu) (hA1 : A1 S mu) (i : Fin n1) :
    ∑ k, (S.u k i) ^ 2 <= mu ^ 2 * (r : Real) / (n1 : Real) := by
  rw [← sign_row_sq_sum_eq_leverage S i]
  have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    sign_sq_le_of_A1 S mu hmu hA1 i j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  convert h using 1
  all_goals first | rfl | field_simp | ring

theorem column_leverage_le_of_A1 {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (mu : Real) (hn1 : 0 < n1) (hn2 : 0 < n2)
    (hmu : 0 <= mu) (hA1 : A1 S mu) (j : Fin n2) :
    ∑ k, (S.v k j) ^ 2 <= mu ^ 2 * (r : Real) / (n2 : Real) := by
  rw [← sign_column_sq_sum_eq_leverage S j]
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    sign_sq_le_of_A1 S mu hmu hA1 i j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  convert h using 1
  all_goals first | rfl | field_simp | ring

end MatrixThreshold

/- Complete locally authored component: ScalarThreshold.lean; SHA256 6ef08a8823e0d0657dd94e4c7970bf23b1e35b056049a77a720e3424114a9ea1. -/

namespace MatrixCompletion

theorem spectralNorm_nonneg {n1 n2 : Nat} (X : RealMatrix n1 n2) :
    0 <= spectralNorm X := norm_nonneg _

theorem spectralNorm_smul {n1 n2 : Nat} (c : Real) (X : RealMatrix n1 n2) :
    spectralNorm (c • X) = |c| * spectralNorm X := by
  simp [spectralNorm, map_smul, norm_smul, Real.norm_eq_abs]

theorem mul_sqrt_mul_sqrt_le_one (a x y : Real)
    (ha : 0 <= a) (hx : 0 <= x) (hy : 0 <= y)
    (h : a ^ 2 * x * y <= 1) :
    a * Real.sqrt x * Real.sqrt y <= 1 := by
  have hs : (a * Real.sqrt x * Real.sqrt y) ^ 2 = a ^ 2 * x * y := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hy]
  have hn : 0 <= a * Real.sqrt x * Real.sqrt y := by positivity
  nlinarith

theorem scalar_threshold (mu N n r L p lam : Real)
    (hmu : 0 <= mu) (hN : 0 < N) (hn : 0 <= n) (hr : 0 <= r)
    (hL : 0 < L) (hp : 0 < p) (hlam : 1 <= lam)
    (hscale : lam * mu ^ 2 * n * r * L <= p * N) :
    p⁻¹ * Real.sqrt ((L * n) / p) *
        (2 * mu ^ 3 * Real.sqrt (r / N) * r * n / N) <=
      2 / (lam * L) := by
  have hlamp : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
  have hpn : 0 < p * N := mul_pos hp hN
  have hlL : 0 < lam * L := mul_pos hlamp hL
  have hcoef : 0 <= mu ^ 2 * n * r * L := by positivity
  have hsmall : mu ^ 2 * n * r * L <= p * N := by
    have h := mul_nonneg (sub_nonneg.mpr hlam) hcoef
    nlinarith [hscale]
  have hsmall' : (mu ^ 2 * n * r * L) / (p * N) <= 1 := by
    apply (div_le_iff₀ hpn).2
    simpa using hsmall
  have heq : mu ^ 2 * (r / N) * ((L * n) / p) =
      (mu ^ 2 * n * r * L) / (p * N) := by
    all_goals first | rfl | field_simp | ring
  have hunit : mu * Real.sqrt (r / N) * Real.sqrt ((L * n) / p) <= 1 := by
    apply mul_sqrt_mul_sqrt_le_one mu (r / N) ((L * n) / p) hmu
      (by positivity) (by positivity)
    simpa only [heq] using hsmall'
  have hbase : (mu ^ 2 * n * r) / (p * N) <= 1 / (lam * L) := by
    apply (div_le_div_iff₀ hpn hlL).2
    nlinarith [hscale]
  have hfactor : p⁻¹ * Real.sqrt ((L * n) / p) *
      (2 * mu ^ 3 * Real.sqrt (r / N) * r * n / N) =
      (2 * ((mu ^ 2 * n * r) / (p * N))) *
        (mu * Real.sqrt (r / N) * Real.sqrt ((L * n) / p)) := by
    all_goals first | rfl | field_simp | ring
  rw [hfactor]
  calc
    (2 * ((mu ^ 2 * n * r) / (p * N))) *
        (mu * Real.sqrt (r / N) * Real.sqrt ((L * n) / p)) <=
        (2 * ((mu ^ 2 * n * r) / (p * N))) * 1 :=
      mul_le_mul_of_nonneg_left hunit (by positivity)
    _ <= 2 / (lam * L) := by
      convert mul_le_mul_of_nonneg_left hbase (by norm_num : (0 : Real) <= 2) using 1 <;> all_goals first | rfl | ring | field_simp

end MatrixCompletion

/- Complete locally authored component: TangentDiagonalBound.lean; SHA256 255b655e54ca6317f60411075a5ca8380fd94644ab57adf78fc0503b47b5528b. -/

namespace MatrixThreshold

open MatrixCompletion
open scoped BigOperators

theorem matrixInner_coordinateMatrix {n1 n2 : Nat}
    (X : RealMatrix n1 n2) (i : Fin n1) (j : Fin n2) :
    matrixInner X (coordinateMatrix i j) = X i j := by
  classical
  simp [matrixInner, coordinateMatrix, ite_and]

theorem tangentCoordinateKernel_diagonal {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (S : SVD M r) (i : Fin n1) (j : Fin n2) :
    tangentCoordinateKernel S i j i j =
      (∑ k, (S.u k i) ^ 2) + (∑ k, (S.v k j) ^ 2) -
        (∑ k, (S.u k i) ^ 2) * (∑ k, (S.v k j) ^ 2) := by
  classical
  rw [tangentCoordinateKernel, matrixInner_coordinateMatrix]
  simp [tangentProjection, leftSingularProjection, rightSingularProjection,
    twoSidedSingularProjection, coordinateMatrix, ite_and, pow_two,
    Finset.sum_mul]

theorem tangentCoordinateKernel_diagonal_abs_le {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (S : SVD M r) (i : Fin n1) (j : Fin n2) :
    |tangentCoordinateKernel S i j i j| <=
      (∑ k, (S.u k i) ^ 2) + (∑ k, (S.v k j) ^ 2) := by
  have hu0 : 0 <= ∑ k, (S.u k i) ^ 2 := Finset.sum_nonneg (by intros; positivity)
  have hv0 : 0 <= ∑ k, (S.v k j) ^ 2 := Finset.sum_nonneg (by intros; positivity)
  have hv1 := column_leverage_le_one S j
  rw [tangentCoordinateKernel_diagonal]
  have hnonneg : 0 <= (∑ k, (S.u k i) ^ 2) + (∑ k, (S.v k j) ^ 2) -
      (∑ k, (S.u k i) ^ 2) * (∑ k, (S.v k j) ^ 2) := by
    nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hv1)]
  rw [abs_of_nonneg hnonneg]
  nlinarith [mul_nonneg hu0 hv0]

theorem diagonal_base_entrySupNorm_le_sum {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (S : SVD M r) (mu : Real)
    (hn1 : 0 < n1) (hn2 : 0 < n2) (hmu : 0 <= mu) (hA1 : A1 S mu) :
    entrySupNorm (linearNeumannDiagonalBaseMatrix S) <=
      mu ^ 3 * Real.sqrt ((r : Real) / ((n1 : Real) * (n2 : Real))) *
        (r : Real) * ((n1 : Real) + (n2 : Real)) / ((n1 : Real) * (n2 : Real)) := by
  haveI : Nonempty (Fin n1) := ⟨⟨0, hn1⟩⟩
  haveI : Nonempty (Fin n2) := ⟨⟨0, hn2⟩⟩
  have hn1r : (n1 : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn1)
  have hn2r : (n2 : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn2)
  unfold entrySupNorm
  apply ciSup_le
  intro i
  apply ciSup_le
  intro j
  have hkernel : |tangentCoordinateKernel S i j i j| <=
      mu ^ 2 * (r : Real) / (n1 : Real) + mu ^ 2 * (r : Real) / (n2 : Real) :=
    (tangentCoordinateKernel_diagonal_abs_le S i j).trans
      (add_le_add (row_leverage_le_of_A1 S mu hn1 hn2 hmu hA1 i)
        (column_leverage_le_of_A1 S mu hn1 hn2 hmu hA1 j))
  change |signMatrix S i j * tangentCoordinateKernel S i j i j| <= _
  rw [abs_mul]
  calc
    |signMatrix S i j| * |tangentCoordinateKernel S i j i j| <=
        (mu * Real.sqrt ((r : Real) / ((n1 : Real) * (n2 : Real)))) *
          (mu ^ 2 * (r : Real) / (n1 : Real) + mu ^ 2 * (r : Real) / (n2 : Real)) :=
      mul_le_mul (hA1 i j) hkernel (abs_nonneg _)
        (mul_nonneg hmu (Real.sqrt_nonneg _))
    _ = _ := by field_simp [hn1r, hn2r]; ring

theorem diagonal_base_entrySupNorm_le {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (S : SVD M r) (mu : Real)
    (hn1 : 0 < n1) (hn2 : 0 < n2) (hmu : 0 <= mu) (hA1 : A1 S mu) :
    entrySupNorm (linearNeumannDiagonalBaseMatrix S) <=
      2 * mu ^ 3 * Real.sqrt ((r : Real) / ((n1 : Real) * (n2 : Real))) *
        (r : Real) * (max n1 n2 : Nat) / ((n1 : Real) * (n2 : Real)) := by
  have h1 : (n1 : Real) <= (max n1 n2 : Nat) := by exact_mod_cast (Nat.le_max_left n1 n2)
  have h2 : (n2 : Real) <= (max n1 n2 : Nat) := by exact_mod_cast (Nat.le_max_right n1 n2)
  have hsum : (n1 : Real) + (n2 : Real) <= 2 * (max n1 n2 : Nat) := by linarith
  refine (diagonal_base_entrySupNorm_le_sum S mu hn1 hn2 hmu hA1).trans ?_
  have hcoef : 0 <= mu ^ 3 * Real.sqrt ((r : Real) / ((n1 : Real) * (n2 : Real))) *
      (r : Real) := by positivity
  have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hcoef)
    (show 0 <= (n1 : Real) * (n2 : Real) by positivity)
  convert h using 1
  all_goals first | rfl | ring | field_simp

end MatrixThreshold

/- Complete locally authored component: Conclusion.lean; SHA256 6947c723de80e5d2097bba8421982b2390d539b3b5994c930cc34f409c489fb3. -/

open MatrixCompletion

set_option linter.unusedVariables false in
theorem solution
    (Cfixed Cbase : ℝ) :
    0 < Cfixed → 0 < Cbase →
    ∃ Cthreshold : ℝ, 0 < Cthreshold ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * μ₁ * max (Real.sqrt μ₀) μ₁ *
            (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        ∀ Omega : Finset (Fin n₁ × Fin n₂),
        linearNeumannDiagonalCenteredContribution Omega S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
          (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹ *
              (1 - 2 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) •
            centeredSamplingFluctuation Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (linearNeumannDiagonalBaseMatrix S) →
        entrySupNorm (linearNeumannDiagonalBaseMatrix S) ≤
          Cbase * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (μ₀ * (r : ℝ) / (↑(max n₁ n₂))) →
        CenteredSamplingSpectralBound Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (linearNeumannDiagonalBaseMatrix S)
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm (linearNeumannDiagonalBaseMatrix S)) →
        spectralNorm
            (linearNeumannDiagonalCenteredContribution Omega S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          Cthreshold * Real.rpow lam (-1) := by
  intro hfixed hbase
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨2 * Cfixed / Real.log 2, by positivity, ?_⟩
  intro β lam hβ hlam n1 n2 r m M mu0 mu S hn1 hn2 hr hm hmu0 hmu hA0 hA1
    hsample Omega hrepr hbaseBound hspectral
  let N : Real := (n1 : Real) * (n2 : Real)
  let n : Real := (max n1 n2 : Nat)
  let L : Real := β * Real.log n
  let p : Real := (m : Real) / N
  have hN : 0 < N := mul_pos (Nat.cast_pos.mpr hn1) (Nat.cast_pos.mpr hn2)
  have hp0 : 0 <= p := div_nonneg (Nat.cast_nonneg _) hN.le
  have hp1 : p <= 1 := (div_le_one hN).mpr (by dsimp [N]; exact_mod_cast hm)
  have hlamp : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
  have hmu' : 0 <= mu := le_trans zero_le_one hmu
  have hrepr' : linearNeumannDiagonalCenteredContribution Omega S p =
      (p⁻¹ * (1 - 2 * p)) •
        centeredSamplingFluctuation Omega p (linearNeumannDiagonalBaseMatrix S) := hrepr
  change spectralNorm (linearNeumannDiagonalCenteredContribution Omega S p) <= _
  by_cases hpzero : p = 0
  · rw [hrepr', MatrixCompletion.spectralNorm_smul, hpzero]
    simp only [inv_zero, zero_mul, abs_zero]
    rw [Real.rpow_eq_pow, Real.rpow_neg_one]
    positivity
  have hp : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hpzero)
  by_cases hnmax : max n1 n2 = 1
  · have hzero : spectralNorm
        (centeredSamplingFluctuation Omega p (linearNeumannDiagonalBaseMatrix S)) = 0 := by
      apply le_antisymm
      · simpa [CenteredSamplingSpectralBound, hnmax, p, N] using hspectral
      · exact MatrixCompletion.spectralNorm_nonneg _
    rw [hrepr', MatrixCompletion.spectralNorm_smul, hzero, mul_zero]
    rw [Real.rpow_eq_pow, Real.rpow_neg_one]
    positivity
  have hnmax2 : 2 <= max n1 n2 := by
    have := Nat.le_max_left n1 n2
    omega
  have hn2r : (2 : Real) <= n := by dsimp [n]; exact_mod_cast hnmax2
  have hlog : Real.log 2 <= Real.log n := Real.log_le_log (by norm_num) hn2r
  have hlogn : 0 < Real.log n := lt_of_lt_of_le hlog2 hlog
  have hL : 0 < L := mul_pos (by linarith) hlogn
  have hLlower : Real.log 2 <= L := by
    dsimp [L]
    nlinarith [mul_nonneg (show 0 <= β - 1 by linarith) hlogn.le]
  have hscale : lam * mu ^ 2 * n * (r : Real) * L <= p * N := by
    have hsample' : lam * mu * max (Real.sqrt mu0) mu * n * (r : Real) * L <=
        (m : Real) := hsample
    have hpN : p * N = (m : Real) := by dsimp [p]; field_simp
    rw [hpN]
    calc
      lam * mu ^ 2 * n * (r : Real) * L = lam * mu * mu * n * (r : Real) * L := by ring
      _ <= lam * mu * max (Real.sqrt mu0) mu * n * (r : Real) * L := by
        gcongr
        exact le_max_right _ _
      _ <= _ := hsample'
  have hcenter : spectralNorm
      (centeredSamplingFluctuation Omega p (linearNeumannDiagonalBaseMatrix S)) <=
      Cfixed * Real.sqrt ((L * n) / p) * entrySupNorm (linearNeumannDiagonalBaseMatrix S) := by
    have hLn : L * n = β * n * Real.log n := by dsimp [L]; ring
    rw [hLn]
    exact hspectral
  have hcoef : |p⁻¹ * (1 - 2 * p)| <= p⁻¹ := by
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hp0)]
    have hfactor : |1 - 2 * p| <= 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    simpa using mul_le_mul_of_nonneg_left hfactor (inv_nonneg.mpr hp0)
  have hbase' := MatrixThreshold.diagonal_base_entrySupNorm_le S mu hn1 hn2 hmu' hA1
  change entrySupNorm (linearNeumannDiagonalBaseMatrix S) <=
    2 * mu ^ 3 * Real.sqrt ((r : Real) / N) * (r : Real) * n / N at hbase'
  have hscalar := scalar_threshold mu N n (r : Real) L p lam hmu' hN
    (by positivity) (Nat.cast_nonneg _) hL hp hlam hscale
  calc
    spectralNorm (linearNeumannDiagonalCenteredContribution Omega S p) =
        |p⁻¹ * (1 - 2 * p)| * spectralNorm
          (centeredSamplingFluctuation Omega p (linearNeumannDiagonalBaseMatrix S)) := by
      rw [hrepr', MatrixCompletion.spectralNorm_smul]
    _ <= p⁻¹ * spectralNorm
        (centeredSamplingFluctuation Omega p (linearNeumannDiagonalBaseMatrix S)) :=
      mul_le_mul_of_nonneg_right hcoef (MatrixCompletion.spectralNorm_nonneg _)
    _ <= p⁻¹ * (Cfixed * Real.sqrt ((L * n) / p) *
        entrySupNorm (linearNeumannDiagonalBaseMatrix S)) :=
      mul_le_mul_of_nonneg_left hcenter (inv_nonneg.mpr hp0)
    _ <= p⁻¹ * (Cfixed * Real.sqrt ((L * n) / p) *
        (2 * mu ^ 3 * Real.sqrt ((r : Real) / N) * (r : Real) * n / N)) := by
      gcongr
    _ = Cfixed * (p⁻¹ * Real.sqrt ((L * n) / p) *
        (2 * mu ^ 3 * Real.sqrt ((r : Real) / N) * (r : Real) * n / N)) := by ring
    _ <= Cfixed * (2 / (lam * L)) := mul_le_mul_of_nonneg_left hscalar hfixed.le
    _ <= Cfixed * (2 / (lam * Real.log 2)) := by
      apply mul_le_mul_of_nonneg_left _ hfixed.le
      exact div_le_div_of_nonneg_left (by norm_num) (mul_pos hlamp hlog2)
        (mul_le_mul_of_nonneg_left hLlower hlamp.le)
    _ = (2 * Cfixed / Real.log 2) * Real.rpow lam (-1) := by
      rw [Real.rpow_eq_pow, Real.rpow_neg_one]
      all_goals first | rfl | ring | field_simp

