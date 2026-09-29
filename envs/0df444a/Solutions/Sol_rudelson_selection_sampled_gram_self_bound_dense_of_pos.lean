-- Prove2me | solution 1 for rudelson_selection_sampled_gram_self_bound_dense_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-06-25T07:44:14.64951+00:00
-- url     : https://prove2.me/submissions/c28ec424-90c6-4110-a470-349518b74d62

import Definitions.Def_matrix_completion_tangent
import Theorems.Thm_full_gram_operator_norm_le_one
import Theorems.Thm_centered_gram_operator_norm_le_p_deviation_of_pos
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MatrixCompletion
open scoped Classical BigOperators Matrix Matrix.Norms.L2Operator

/-- Carve A — `rudelson_selection_sampled_gram_self_bound_dense`.

CR2009 §9.1 eq(2.1).  Writing `δ = (δ - p) + p`, the SAMPLED Gram operator
`Gs = ∑ δ_ab T_ab` splits as the CENTERED Gram `Gc = ∑ (δ_ab - p) T_ab` plus
`p` times the FULL Gram `Gf = ∑ T_ab`, where `T_ab = vec(P_T e_ab) ⊗ vec(P_T e_ab)`.
The triangle inequality and `norm_smul` (with `p ≥ 0`) give
`‖Gs‖ ≤ ‖Gc‖ + p·‖Gf‖`, and the two carved facts `‖Gc‖ ≤ p·Z`
(`centered_gram_operator_norm_le_p_deviation`) and `‖Gf‖ ≤ 1`
(`full_gram_operator_norm_le_one`) close it to `p·Z + p·1 = p·(Z+1)`. -/
theorem solution
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (hp : 0 < p) :
    ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
        (∑ ab : Fin n1 × Fin n2,
          (if ab ∈ Omega then (1 : Real) else 0) •
            Matrix.vecMulVec
              (fun e : Fin n1 × Fin n2 =>
                tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
              (fun e : Fin n1 × Fin n2 =>
                tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2))))‖
      ≤ p * (tangentSamplingDeviation Omega S p + 1) := by
  classical
  have hp0 : 0 ≤ p := le_of_lt hp
  -- abbreviations
  set y : (Fin n1 × Fin n2) → (Fin n1 × Fin n2 → Real) :=
    fun ab e => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2 with hy
  set T : (Fin n1 × Fin n2) → Matrix (Fin n1 × Fin n2) (Fin n1 × Fin n2) Real :=
    fun ab => Matrix.vecMulVec (y ab) (y ab) with hT
  -- the three Gram matrices
  set Gs : Matrix (Fin n1 × Fin n2) (Fin n1 × Fin n2) Real :=
    ∑ ab : Fin n1 × Fin n2, (if ab ∈ Omega then (1 : Real) else 0) • T ab with hGs
  set Gf : Matrix (Fin n1 × Fin n2) (Fin n1 × Fin n2) Real :=
    ∑ ab : Fin n1 × Fin n2, (1 : Real) • T ab with hGf
  set Gc : Matrix (Fin n1 × Fin n2) (Fin n1 × Fin n2) Real :=
    ∑ ab : Fin n1 × Fin n2,
      (((if ab ∈ Omega then (1 : Real) else 0) - p) • T ab) with hGc
  -- ALGEBRA: Gs = Gc + p • Gf
  have hsplit : Gs = Gc + p • Gf := by
    rw [hGs, hGc, hGf]
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ab _
    -- ((δ-p)•T) + p•(1•T) = δ•T
    rw [smul_smul, mul_one, ← add_smul]
    congr 1
    ring
  -- rewrite the goal's literal toCLM∘toEuclideanLin norm as the matrix L2 operator norm
  have hnormGs : ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Gs))‖ = ‖Gs‖ :=
    (Matrix.l2_opNorm_def Gs).symm
  rw [show (∑ ab : Fin n1 × Fin n2, (if ab ∈ Omega then (1 : Real) else 0) •
        Matrix.vecMulVec (y ab) (y ab)) = Gs from rfl] at *
  rw [hnormGs, hsplit]
  -- triangle + norm_smul
  refine le_trans (norm_add_le Gc (p • Gf)) ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp0]
  -- Fact (2): ‖Gc‖ ≤ p·Z
  have hGcbound :
      ‖Gc‖ ≤ p * tangentSamplingDeviation Omega S p := by
    have h := centered_gram_operator_norm_le_p_deviation_of_pos S Omega p hp
    rw [Matrix.l2_opNorm_def Gc]
    exact h
  -- Fact (1): ‖Gf‖ ≤ 1
  have hGfbound : ‖Gf‖ ≤ 1 := by
    have h := full_gram_operator_norm_le_one S Omega p
    rw [Matrix.l2_opNorm_def Gf]
    exact h
  -- combine
  have : ‖Gc‖ + p * ‖Gf‖
      ≤ p * tangentSamplingDeviation Omega S p + p * 1 := by
    gcongr
  calc ‖Gc‖ + p * ‖Gf‖
      ≤ p * tangentSamplingDeviation Omega S p + p * 1 := this
    _ = p * (tangentSamplingDeviation Omega S p + 1) := by ring
