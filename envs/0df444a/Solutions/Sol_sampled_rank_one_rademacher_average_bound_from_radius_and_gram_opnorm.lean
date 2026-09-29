-- Prove2me | solution 1 for sampled_rank_one_rademacher_average_bound_from_radius_and_gram_opnorm
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-26T00:22:47.148201+00:00
-- url     : https://prove2.me/submissions/f67f5794-19e5-4a92-bdfe-be7dc257bd60

import Theorems.Thm_reindexed_rademacher_matrix_operator_norm_first_moment_log_window_from_2p
import Theorems.Thm_rank_one_variance_proxy_eigenvalue_le_radius_sq_gram_opnorm
import Theorems.Thm_opnorm_submatrix_equiv
import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.EquivFin

open Matrix MatrixCompletion
open scoped Classical BigOperators Matrix Matrix.Norms.L2Operator

set_option maxHeartbeats 1000000

private theorem vecMulVec_self_isHermitian {α : Type*} [Fintype α]
    (y : α → ℝ) : (Matrix.vecMulVec y y).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [Matrix.vecMulVec_apply, mul_comm]

private theorem hermitian_sum {ι n : Type*} [Fintype ι] [Fintype n]
    (A : ι → Matrix n n ℝ) (hA : ∀ i, (A i).IsHermitian) :
    (∑ i : ι, A i).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp_rw [Matrix.sum_apply]
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact (hA a).apply i j

private theorem hermitian_finset_sum {ι n : Type*} [Fintype n]
    (s : Finset ι) (A : ι → Matrix n n ℝ) (hA : ∀ i ∈ s, (A i).IsHermitian) :
    (∑ i ∈ s, A i).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp_rw [Matrix.sum_apply]
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro a ha
  exact (hA a ha).apply i j

private theorem sampled_rank_one_isHermitian {α : Type*} [Fintype α] [DecidableEq α]
    (Omega : Finset α) (y : α → α → ℝ) (c : α) :
    ((if c ∈ Omega then (1 : ℝ) else 0) • Matrix.vecMulVec (y c) (y c)).IsHermitian := by
  exact (vecMulVec_self_isHermitian (y c)).smul (IsSelfAdjoint.all _)

private theorem signed_indicator_sum_eq {α : Type*} [Fintype α] [DecidableEq α]
    (Omega eps : Finset α) (y : α → α → ℝ) :
    (∑ c : α, (if c ∈ eps then (1 : ℝ) else -1) •
        ((if c ∈ Omega then (1 : ℝ) else 0) • Matrix.vecMulVec (y c) (y c)))
      =
    (∑ c : α, (((if c ∈ eps then (1 : ℝ) else -1) *
        (if c ∈ Omega then (1 : ℝ) else 0)) • Matrix.vecMulVec (y c) (y c))) := by
  apply Finset.sum_congr rfl
  intro c _
  rw [smul_smul]

private theorem submatrix_vecMulVec_equiv {α : Type*} [Fintype α]
    (e : Fin (Fintype.card α) ≃ α) (y : α → ℝ) :
    (Matrix.vecMulVec y y).submatrix e e =
      Matrix.vecMulVec (fun k : Fin (Fintype.card α) => y (e k))
        (fun k : Fin (Fintype.card α) => y (e k)) := by
  ext i j
  simp [Matrix.vecMulVec_apply]

private theorem submatrix_sampled_rank_one {α : Type*} [Fintype α] [DecidableEq α]
    (Omega : Finset α) (y : α → α → ℝ)
    (e : Fin (Fintype.card α) ≃ α) (c : α) :
    (((if c ∈ Omega then (1 : ℝ) else 0) • Matrix.vecMulVec (y c) (y c)).submatrix e e)
      =
    (if c ∈ Omega then (1 : ℝ) else 0) •
      Matrix.vecMulVec (fun k : Fin (Fintype.card α) => y c (e k))
        (fun k : Fin (Fintype.card α) => y c (e k)) := by
  ext i j
  by_cases hc : c ∈ Omega
  · simp [hc, Matrix.vecMulVec_apply, Matrix.submatrix_apply]
  · simp [hc, Matrix.vecMulVec_apply, Matrix.submatrix_apply]

private theorem reindexed_dot_eq {α : Type*} [Fintype α]
    (e : Fin (Fintype.card α) ≃ α) (y : α → ℝ) :
    (fun k : Fin (Fintype.card α) => y (e k)) ⬝ᵥ
        (fun k : Fin (Fintype.card α) => y (e k))
      = y ⬝ᵥ y := by
  rw [dotProduct, dotProduct]
  exact Fintype.sum_equiv e (fun k => y (e k) * y (e k)) (fun k => y k * y k)
    (by intro; rfl)

private theorem sampled_gram_submatrix_eq {α : Type*} [Fintype α] [DecidableEq α]
    (Omega : Finset α) (y : α → α → ℝ)
    (e : Fin (Fintype.card α) ≃ α) :
    (∑ c : α, ((if c ∈ Omega then (1 : ℝ) else 0) •
        Matrix.vecMulVec (y c) (y c))).submatrix e e
      =
    ∑ c ∈ Omega,
      Matrix.vecMulVec (fun k : Fin (Fintype.card α) => y c (e k))
        (fun k : Fin (Fintype.card α) => y c (e k)) := by
  ext i j
  simp_rw [Matrix.submatrix_apply, Matrix.sum_apply]
  simpa [Matrix.vecMulVec_apply] using
    (Finset.sum_filter (s := (Finset.univ : Finset α)) (p := fun c => c ∈ Omega)
      (f := fun c => y c (e i) * y c (e j))).symm

private theorem sampled_variance_submatrix_eq {α : Type*} [Fintype α] [DecidableEq α]
    (Omega : Finset α) (y : α → α → ℝ)
    (e : Fin (Fintype.card α) ≃ α) :
    (∑ c : α,
        (((if c ∈ Omega then (1 : ℝ) else 0) • Matrix.vecMulVec (y c) (y c)).submatrix e e) *
        (((if c ∈ Omega then (1 : ℝ) else 0) • Matrix.vecMulVec (y c) (y c)).submatrix e e))
      =
    ∑ c ∈ Omega,
      Matrix.vecMulVec (fun k : Fin (Fintype.card α) => y c (e k))
          (fun k : Fin (Fintype.card α) => y c (e k)) *
        Matrix.vecMulVec (fun k : Fin (Fintype.card α) => y c (e k))
          (fun k : Fin (Fintype.card α) => y c (e k)) := by
  ext i j
  simp_rw [Matrix.sum_apply]
  let term : α → ℝ := fun c =>
    ((((if c ∈ Omega then (1 : ℝ) else 0) • Matrix.vecMulVec (y c) (y c)).submatrix e e) *
      (((if c ∈ Omega then (1 : ℝ) else 0) • Matrix.vecMulVec (y c) (y c)).submatrix e e)) i j
  have hfilter :
      ∑ c ∈ (Finset.univ : Finset α).filter (fun c => c ∈ Omega), term c =
        ∑ c ∈ (Finset.univ : Finset α), term c := by
    apply Finset.sum_filter_of_ne
    intro c hc hne
    by_contra hco
    have hzero : term c = 0 := by
      simp [term, hco]
    exact hne hzero
  calc
    (∑ c : α,
        ((((if c ∈ Omega then (1 : ℝ) else 0) • Matrix.vecMulVec (y c) (y c)).submatrix e e) *
        (((if c ∈ Omega then (1 : ℝ) else 0) • Matrix.vecMulVec (y c) (y c)).submatrix e e)) i j)
        = ∑ c : α, term c := rfl
    _ = ∑ c ∈ (Finset.univ : Finset α), term c := by simp
    _ = ∑ c ∈ (Finset.univ : Finset α).filter (fun c => c ∈ Omega), term c := hfilter.symm
    _ = ∑ c ∈ Omega,
        (Matrix.vecMulVec (fun k : Fin (Fintype.card α) => y c (e k))
            (fun k : Fin (Fintype.card α) => y c (e k)) *
          Matrix.vecMulVec (fun k : Fin (Fintype.card α) => y c (e k))
            (fun k : Fin (Fintype.card α) => y c (e k))) i j := by
      rw [Finset.filter_univ_mem Omega]
      apply Finset.sum_congr rfl
      intro c hc
      simp [term, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.submatrix_apply, hc]

private theorem sqrt_radius_norm_eq {R normG : ℝ} (hR : 0 ≤ R) :
    Real.sqrt (R ^ 2 * normG) = R * Real.sqrt normG := by
  rw [Real.sqrt_mul (sq_nonneg R)]
  rw [Real.sqrt_sq_eq_abs]
  rw [abs_of_nonneg hR]

theorem solution :
    ∃ Csym0 : ℝ, 0 < Csym0 ∧
      ∀ {α : Type*} [Fintype α] [DecidableEq α] {N : ℕ},
        0 < Fintype.card α → 2 ≤ N → Fintype.card α ≤ N * N →
        ∀ (y : α → α → ℝ) (R : ℝ),
        0 ≤ R →
        (∀ c : α, (y c ⬝ᵥ y c) ≤ R ^ 2) →
        ∀ (Omega : Finset α),
        (∑ eps : Finset α, ((1:ℝ)/2) ^ (Fintype.card α) *
          ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
            (∑ c : α, (((if c ∈ eps then (1:ℝ) else -1) *
                (if c ∈ Omega then (1:ℝ) else 0)) •
              Matrix.vecMulVec (y c) (y c)))))‖)
        ≤ Csym0 *
            (Real.sqrt (Real.log (N : ℝ)) * R) *
            Real.sqrt
              ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
                (∑ c : α, (if c ∈ Omega then (1:ℝ) else 0) •
                  Matrix.vecMulVec (y c) (y c))))‖ := by
  rcases reindexed_rademacher_matrix_operator_norm_first_moment_log_window_from_2p with
    ⟨Clog, hClog_pos, hClog⟩
  refine ⟨Clog, hClog_pos, ?_⟩
  intro α _ _ N hcard_pos hN hcard_le y R hR hRadius Omega
  let H : α → Matrix α α ℝ :=
    fun c => (if c ∈ Omega then (1 : ℝ) else 0) • Matrix.vecMulVec (y c) (y c)
  let e : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  let yfin : α → Fin (Fintype.card α) → ℝ := fun c k => y c (e k)
  let Gfin : Matrix (Fin (Fintype.card α)) (Fin (Fintype.card α)) ℝ :=
    ∑ c ∈ Omega, Matrix.vecMulVec (yfin c) (yfin c)
  let Vfin : Matrix (Fin (Fintype.card α)) (Fin (Fintype.card α)) ℝ :=
    ∑ c ∈ Omega, Matrix.vecMulVec (yfin c) (yfin c) * Matrix.vecMulVec (yfin c) (yfin c)
  let normG : ℝ := ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
    (∑ c : α, (if c ∈ Omega then (1:ℝ) else 0) • Matrix.vecMulVec (y c) (y c))))‖
  have hHHerm : ∀ c, (H c).IsHermitian := by
    intro c
    exact sampled_rank_one_isHermitian Omega y c
  have hVeq :
      (∑ c : α, ((H c).submatrix e e) * ((H c).submatrix e e)) = Vfin := by
    simpa [H, Vfin, yfin] using sampled_variance_submatrix_eq Omega y e
  have hVHermDirect : Vfin.IsHermitian := by
    dsimp [Vfin]
    exact hermitian_finset_sum Omega
      (fun c => Matrix.vecMulVec (yfin c) (yfin c) * Matrix.vecMulVec (yfin c) (yfin c))
      (by
        intro c hc
        have hbase := vecMulVec_self_isHermitian (yfin c)
        have hself := Matrix.isHermitian_conjTranspose_mul_self
          (Matrix.vecMulVec (yfin c) (yfin c))
        simpa [hbase.eq] using hself)
  have hVHerm : (∑ c : α, ((H c).submatrix e e) * ((H c).submatrix e e)).IsHermitian := by
    rw [hVeq]
    exact hVHermDirect
  have hGsub :
      ((∑ c : α, (if c ∈ Omega then (1:ℝ) else 0) •
        Matrix.vecMulVec (y c) (y c)).submatrix e e) = Gfin := by
    simpa [Gfin, yfin] using sampled_gram_submatrix_eq Omega y e
  have hGHerm : Gfin.IsHermitian := by
    dsimp [Gfin]
    exact hermitian_finset_sum Omega (fun c => Matrix.vecMulVec (yfin c) (yfin c))
      (by intro c hc; exact vecMulVec_self_isHermitian (yfin c))
  have hRadiusFin : ∀ c ∈ Omega, (yfin c ⬝ᵥ yfin c) ≤ R ^ 2 := by
    intro c hc
    simpa [yfin, reindexed_dot_eq e (y c)] using hRadius c
  have hVarRaw :=
    rank_one_variance_proxy_eigenvalue_le_radius_sq_gram_opnorm
      (d := Fintype.card α) (ι := α) Omega yfin R hR hRadiusFin hGHerm hVHermDirect
  have hGnorm_eq : ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Gfin))‖ = normG := by
    have hop :=
      opnorm_submatrix_equiv e
        (∑ c : α, (if c ∈ Omega then (1:ℝ) else 0) • Matrix.vecMulVec (y c) (y c))
    rw [hGsub] at hop
    simpa [normG, MatrixCompletion.spectralNorm] using hop
  have hEig :
      ∀ i,
        hVHerm.eigenvalues i ≤ R ^ 2 * normG := by
    intro i
    have hi := hVarRaw i
    rw [hGnorm_eq] at hi
    have hEigFun : hVHerm.eigenvalues = hVHermDirect.eigenvalues := by
      rw [Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff]
      exact congrArg Matrix.charpoly hVeq
    rw [hEigFun]
    exact hi
  have hnormV_nonneg : 0 ≤ R ^ 2 * normG := by
    exact mul_nonneg (sq_nonneg R) (norm_nonneg _)
  have hLog :=
    hClog (α := α) (ι := α) (N := N)
      hcard_pos hN hcard_le H hHHerm (R ^ 2 * normG) hnormV_nonneg hVHerm hEig
  have hLHS :
      (∑ eps : Finset α, ((1:ℝ)/2) ^ (Fintype.card α) *
          ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
            (∑ c : α, (if c ∈ eps then (1:ℝ) else -1) • H c)))‖)
        =
      (∑ eps : Finset α, ((1:ℝ)/2) ^ (Fintype.card α) *
          ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
            (∑ c : α, (((if c ∈ eps then (1:ℝ) else -1) *
                (if c ∈ Omega then (1:ℝ) else 0)) •
              Matrix.vecMulVec (y c) (y c)))))‖) := by
    apply Finset.sum_congr rfl
    intro eps _
    congr 1
    rw [signed_indicator_sum_eq Omega eps y]
  have hSqrt :
      Real.sqrt (R ^ 2 * normG) = R * Real.sqrt normG := by
    exact sqrt_radius_norm_eq hR
  rw [hLHS] at hLog
  calc
    (∑ eps : Finset α, ((1:ℝ)/2) ^ (Fintype.card α) *
          ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
            (∑ c : α, (((if c ∈ eps then (1:ℝ) else -1) *
                (if c ∈ Omega then (1:ℝ) else 0)) •
              Matrix.vecMulVec (y c) (y c)))))‖)
        ≤ Clog * Real.sqrt (Real.log (N : ℝ)) * Real.sqrt (R ^ 2 * normG) := hLog
    _ = Clog * (Real.sqrt (Real.log (N : ℝ)) * R) * Real.sqrt normG := by
      rw [hSqrt]
      ring
