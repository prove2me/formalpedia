-- Prove2me | solution 1 for full_gram_operator_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-06-25T07:41:00.852214+00:00
-- url     : https://prove2.me/submissions/d36bce45-6ecc-41d8-af62-b311022ca9ed

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Theorems.Thm_tangent_projection_idempotent
import Theorems.Thm_tangent_projection_self_adjoint
import Theorems.Thm_hs_vectorization_isometry_intertwines_rank_one_tangent

open MatrixCompletion
open scoped Classical BigOperators Matrix Matrix.Norms.L2Operator

namespace FullGramSol

/-- Frobenius inner product picks out the entry against a coordinate matrix. -/
theorem matrixInner_coordinateMatrix {n1 n2 : Nat} (a : Fin n1) (b : Fin n2)
    (K : RealMatrix n1 n2) : matrixInner (coordinateMatrix a b) K = K a b := by
  unfold matrixInner coordinateMatrix
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro c _ hc; simp [hc]
    · intro h; exact absurd (Finset.mem_univ b) h
  · intro c _ hc
    apply Finset.sum_eq_zero
    intro d _
    have : ¬ (c = a ∧ d = b) := by tauto
    simp [this]
  · intro h; exact absurd (Finset.mem_univ a) h

theorem matrixInner_coordinateMatrix' {n1 n2 : Nat} (a : Fin n1) (b : Fin n2)
    (K : RealMatrix n1 n2) : matrixInner K (coordinateMatrix a b) = K a b := by
  unfold matrixInner coordinateMatrix
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro c _ hc; simp [hc]
    · intro h; exact absurd (Finset.mem_univ b) h
  · intro c _ hc
    apply Finset.sum_eq_zero
    intro d _
    have : ¬ (c = a ∧ d = b) := by tauto
    simp [this]
  · intro h; exact absurd (Finset.mem_univ a) h

theorem matrixInner_comm {n1 n2 : Nat} (X Y : RealMatrix n1 n2) :
    matrixInner X Y = matrixInner Y X := by
  unfold matrixInner; congr 1; ext i; congr 1; ext j; ring

theorem frobeniusNormSq_nonneg {n1 n2 : Nat} (X : RealMatrix n1 n2) :
    0 ≤ frobeniusNormSq X := by
  unfold frobeniusNormSq
  apply Finset.sum_nonneg; intro i _; apply Finset.sum_nonneg; intro j _; positivity

/-- The full Gram operator acts as the vectorized tangent projection:
`Gf *ᵥ vec H = vec (P_T H)`. -/
theorem frame_identity {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (H : RealMatrix n1 n2) :
    (∑ ab : Fin n1 × Fin n2,
        (1 : Real) • Matrix.vecMulVec
          (fun e : Fin n1 × Fin n2 => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
          (fun e : Fin n1 × Fin n2 => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)).mulVec
      (fun e : Fin n1 × Fin n2 => H e.1 e.2)
      = (fun e : Fin n1 × Fin n2 => tangentProjection S H e.1 e.2) := by
  obtain ⟨_, _, hiii⟩ := hs_vectorization_isometry_intertwines_rank_one_tangent S
  funext cd
  rw [Matrix.sum_mulVec]
  simp only [one_smul, Finset.sum_apply]
  have hstep : ∀ ab : Fin n1 × Fin n2,
      (Matrix.vecMulVec
          (fun e : Fin n1 × Fin n2 => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
          (fun e : Fin n1 × Fin n2 => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)).mulVec
        (fun e : Fin n1 × Fin n2 => H e.1 e.2) cd
      = (matrixInner (tangentProjection S (coordinateMatrix ab.1 ab.2)) H)
          * (tangentProjection S (coordinateMatrix ab.1 ab.2) cd.1 cd.2) := by
    intro ab
    rw [hiii ab.1 ab.2 H]
    simp [Pi.smul_apply, smul_eq_mul]
  simp only [hstep]
  have hsum : ∀ ab : Fin n1 × Fin n2,
      (matrixInner (tangentProjection S (coordinateMatrix ab.1 ab.2)) H)
          * (tangentProjection S (coordinateMatrix ab.1 ab.2) cd.1 cd.2)
      = (tangentProjection S H) ab.1 ab.2
          * (tangentProjection S (coordinateMatrix cd.1 cd.2)) ab.1 ab.2 := by
    intro ab
    congr 1
    · rw [tangent_projection_self_adjoint, matrixInner_coordinateMatrix]
    · have : tangentProjection S (coordinateMatrix ab.1 ab.2) cd.1 cd.2
          = matrixInner (coordinateMatrix cd.1 cd.2)
              (tangentProjection S (coordinateMatrix ab.1 ab.2)) := by
        rw [matrixInner_coordinateMatrix]
      rw [this, matrixInner_comm, tangent_projection_self_adjoint, matrixInner_coordinateMatrix]
  rw [Finset.sum_congr rfl (fun ab _ => hsum ab)]
  have : ∑ ab : Fin n1 × Fin n2,
      (tangentProjection S H) ab.1 ab.2
        * (tangentProjection S (coordinateMatrix cd.1 cd.2)) ab.1 ab.2
      = matrixInner (tangentProjection S H)
          (tangentProjection S (coordinateMatrix cd.1 cd.2)) := by
    unfold matrixInner; rw [Fintype.sum_prod_type]
  rw [this, tangent_projection_self_adjoint, tangent_projection_idempotent,
    ← tangent_projection_self_adjoint, matrixInner_coordinateMatrix']

/-- Euclidean norm squared equals the self–dot–product of `ofLp`. -/
theorem euclid_normSq {ι : Type*} [Fintype ι] [DecidableEq ι] (z : EuclideanSpace ℝ ι) :
    ‖z‖ ^ 2 = (fun i => z i) ⬝ᵥ (fun i => z i) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [PiLp.inner_apply, dotProduct]
  rfl

/-- Cauchy–Schwarz / contraction: `‖P_T H‖²_F ≤ ‖H‖²_F`. -/
theorem matrixInner_sq_le {n1 n2 : Nat} (X Y : RealMatrix n1 n2) :
    (matrixInner X Y) ^ 2 ≤ frobeniusNormSq X * frobeniusNormSq Y := by
  have hX : frobeniusNormSq X = ∑ ab : Fin n1 × Fin n2, (X ab.1 ab.2) ^ 2 := by
    unfold frobeniusNormSq; rw [Fintype.sum_prod_type]
  have hY : frobeniusNormSq Y = ∑ ab : Fin n1 × Fin n2, (Y ab.1 ab.2) ^ 2 := by
    unfold frobeniusNormSq; rw [Fintype.sum_prod_type]
  have hI : matrixInner X Y = ∑ ab : Fin n1 × Fin n2, (X ab.1 ab.2) * (Y ab.1 ab.2) := by
    unfold matrixInner; rw [Fintype.sum_prod_type]
  rw [hX, hY, hI]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun ab : Fin n1 × Fin n2 => X ab.1 ab.2) (fun ab : Fin n1 × Fin n2 => Y ab.1 ab.2)

theorem tangent_contraction {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (H : RealMatrix n1 n2) :
    frobeniusNormSq (tangentProjection S H) ≤ frobeniusNormSq H := by
  have hkey : frobeniusNormSq (tangentProjection S H)
      = matrixInner H (tangentProjection S H) := by
    have : frobeniusNormSq (tangentProjection S H)
        = matrixInner (tangentProjection S H) (tangentProjection S H) := by
      unfold frobeniusNormSq matrixInner; congr 1; ext i; congr 1; ext j; ring
    rw [this, matrixInner_comm, tangent_projection_self_adjoint, tangent_projection_idempotent,
      matrixInner_comm]
  have hnn : 0 ≤ frobeniusNormSq (tangentProjection S H) := frobeniusNormSq_nonneg _
  have hcs : (matrixInner H (tangentProjection S H)) ^ 2
      ≤ frobeniusNormSq H * frobeniusNormSq (tangentProjection S H) :=
    matrixInner_sq_le H (tangentProjection S H)
  rw [← hkey] at hcs
  rcases eq_or_lt_of_le hnn with h0 | hpos
  · rw [← h0]; exact frobeniusNormSq_nonneg _
  · apply le_of_mul_le_mul_right _ hpos
    rw [← sq]; exact hcs

end FullGramSol

open FullGramSol

/-- Fact (1) of CR2009 §9.1 eq(2.1): the FULL Gram operator
`Gf = ∑_{ab} vec(P_T e_ab) ⊗ vec(P_T e_ab)` is the vectorized orthogonal tangent
projector `P_T`, hence its operator norm is at most `1`. -/
theorem solution
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) :
    ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
        (∑ ab : Fin n1 × Fin n2,
          (1 : Real) •
            Matrix.vecMulVec
              (fun e : Fin n1 × Fin n2 =>
                tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
              (fun e : Fin n1 × Fin n2 =>
                tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2))))‖
      ≤ 1 := by
  -- Name the Gram matrix.
  set Gf : Matrix (Fin n1 × Fin n2) (Fin n1 × Fin n2) Real :=
    ∑ ab : Fin n1 × Fin n2,
      (1 : Real) •
        Matrix.vecMulVec
          (fun e : Fin n1 × Fin n2 => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
          (fun e : Fin n1 × Fin n2 => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
    with hGf
  -- The target is the operator norm of `toEuclideanCLM Gf`.
  have hnorm : ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Gf))‖
      = ‖Matrix.toEuclideanCLM (n := Fin n1 × Fin n2) (𝕜 := ℝ) Gf‖ := rfl
  rw [hnorm]
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) ?_
  intro x
  -- the underlying matrix of x
  set H : RealMatrix n1 n2 := fun i j => x (i, j) with hH
  -- ofLp x = vec H
  have hofLp : (WithLp.ofLp x) = (fun e : Fin n1 × Fin n2 => H e.1 e.2) := by
    funext e; rfl
  -- image
  have himg : (WithLp.ofLp (Matrix.toEuclideanCLM (n := Fin n1 × Fin n2) (𝕜 := ℝ) Gf x))
      = (fun e : Fin n1 × Fin n2 => tangentProjection S H e.1 e.2) := by
    rw [Matrix.ofLp_toEuclideanCLM, hofLp, hGf]
    exact frame_identity S H
  -- norms squared
  have hxsq : ‖x‖ ^ 2 = frobeniusNormSq H := by
    rw [euclid_normSq]
    have : frobeniusNormSq H = (fun e : Fin n1 × Fin n2 => H e.1 e.2)
        ⬝ᵥ (fun e : Fin n1 × Fin n2 => H e.1 e.2) := by
      obtain ⟨_, hii, _⟩ := hs_vectorization_isometry_intertwines_rank_one_tangent S
      exact hii H
    rw [this]
  have hzsq : ‖Matrix.toEuclideanCLM (n := Fin n1 × Fin n2) (𝕜 := ℝ) Gf x‖ ^ 2
      = frobeniusNormSq (tangentProjection S H) := by
    rw [euclid_normSq]
    have hdot : (fun i => (Matrix.toEuclideanCLM (n := Fin n1 × Fin n2) (𝕜 := ℝ) Gf x) i)
        = (fun e : Fin n1 × Fin n2 => tangentProjection S H e.1 e.2) := by
      funext e; exact congrFun himg e
    rw [hdot]
    obtain ⟨_, hii, _⟩ := hs_vectorization_isometry_intertwines_rank_one_tangent S
    rw [hii (tangentProjection S H)]
  -- ‖z‖² ≤ ‖x‖²  ⟹  ‖z‖ ≤ ‖x‖ = 1 * ‖x‖
  have hsq_le : ‖Matrix.toEuclideanCLM (n := Fin n1 × Fin n2) (𝕜 := ℝ) Gf x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [hzsq, hxsq]; exact tangent_contraction S H
  have hle : ‖Matrix.toEuclideanCLM (n := Fin n1 × Fin n2) (𝕜 := ℝ) Gf x‖ ≤ ‖x‖ := by
    have h1 : (0:ℝ) ≤ ‖Matrix.toEuclideanCLM (n := Fin n1 × Fin n2) (𝕜 := ℝ) Gf x‖ := norm_nonneg _
    have h2 : (0:ℝ) ≤ ‖x‖ := norm_nonneg _
    nlinarith [hsq_le, h1, h2]
  rw [one_mul]; exact hle
