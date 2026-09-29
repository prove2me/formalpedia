-- Prove2me | solution 1 for dlp_conditional_lemma2_sigma_fiber_matrix_chaos_order3
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-23T20:58:19.890446+00:00
-- url     : https://prove2.me/submissions/4cb85c47-d972-4b44-9957-8837570612fd

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_rademacher
import Mathlib.Analysis.InnerProductSpace.Basic
import Theorems.Thm_rademacher_trilinear_chaos_l4_l2_bonami_hypercontractivity
import Theorems.Thm_rademacher_lower_tail_positivity_from_l4_l2_hypercontractivity

open MatrixCompletion
open scoped BigOperators Classical InnerProductSpace

theorem solution
    {n1 n2 : Nat}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (T : RealMatrix n1 n2)
    (xv : EuclideanSpace ℝ (Fin n2)) (yv : EuclideanSpace ℝ (Fin n1))
    (hxv : ‖xv‖ ≤ 1) (hyv : ‖yv‖ ≤ 1)
    (hnorm : ⟪Matrix.toEuclideanLin T xv, yv⟫_ℝ = spectralNorm T)
    (hmean :
      rademacherExpectation
        (fun eps => ⟪Matrix.toEuclideanLin
          (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
            (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
             else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
                    * rademacherSign eps w3.1 w3.2) • a w1 w2 w3)) xv, yv⟫_ℝ) = 0)
    (hvar :
      0 < rademacherExpectation
        (fun eps => (⟪Matrix.toEuclideanLin
          (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
            (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
             else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
                    * rademacherSign eps w3.1 w3.2) • a w1 w2 w3)) xv, yv⟫_ℝ) ^ 2)) :
    rademacherExpectation
        (fun eps =>
          if spectralNorm T ≤ spectralNorm (T +
            (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
              (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
               else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
                      * rademacherSign eps w3.1 w3.2) • a w1 w2 w3)))
          then (1 : ℝ) else 0) ≥ 1 / 2916 := by
  have spec_lb : ∀ {n1 n2 : Nat} (X : RealMatrix n1 n2)
    (xv : EuclideanSpace ℝ (Fin n2)) (yv : EuclideanSpace ℝ (Fin n1))
    (hxv : ‖xv‖ ≤ 1) (hyv : ‖yv‖ ≤ 1), ⟪Matrix.toEuclideanLin X xv, yv⟫_ℝ ≤ spectralNorm X := by
    intro n1 n2 X xv yv hxv hyv
    unfold spectralNorm
    calc ⟪Matrix.toEuclideanLin X xv, yv⟫_ℝ
        ≤ ‖Matrix.toEuclideanLin X xv‖ * ‖yv‖ := real_inner_le_norm _ _
      _ ≤ ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X)‖ * ‖xv‖ * ‖yv‖ := by
          gcongr
          exact (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X)).le_opNorm xv
      _ ≤ ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X)‖ * 1 * 1 := by
          have hop : (0:ℝ) ≤ ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X)‖ := norm_nonneg _
          gcongr
      _ = ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X)‖ := by ring
  -- bridge: matrix chaos inner product = scalar trilinear chaos with coeff ⟪a xv,yv⟫
  have bridge : ∀ (eps : Finset (Fin n1 × Fin n2)),
      (⟪Matrix.toEuclideanLin
          (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
            (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
             else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
                    * rademacherSign eps w3.1 w3.2) • a w1 w2 w3)) xv, yv⟫_ℝ)
        = ∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
            (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : ℝ)
             else (⟪Matrix.toEuclideanLin (a w1 w2 w3) xv, yv⟫_ℝ) * rademacherSign eps w1.1 w1.2
                    * rademacherSign eps w2.1 w2.2 * rademacherSign eps w3.1 w3.2) := by
    intro eps
    rw [map_sum, LinearMap.sum_apply, sum_inner]
    refine Finset.sum_congr rfl (fun w1 _ => ?_)
    rw [map_sum, LinearMap.sum_apply, sum_inner]
    refine Finset.sum_congr rfl (fun w2 _ => ?_)
    rw [map_sum, LinearMap.sum_apply, sum_inner]
    refine Finset.sum_congr rfl (fun w3 _ => ?_)
    by_cases h : w1 = w2 ∨ w1 = w3 ∨ w2 = w3
    · simp [h]
    · rw [if_neg h, if_neg h, map_smul, LinearMap.smul_apply, inner_smul_left]
      simp only [RCLike.conj_to_real]; ring
  -- scalar chaos F := the bridged scalar trilinear chaos
  set acoef : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → ℝ :=
    fun w1 w2 w3 => ⟪Matrix.toEuclideanLin (a w1 w2 w3) xv, yv⟫_ℝ with hacoef
  set F : Finset (Fin n1 × Fin n2) → ℝ :=
    fun eps => ∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
      (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : ℝ)
       else acoef w1 w2 w3 * rademacherSign eps w1.1 w1.2
              * rademacherSign eps w2.1 w2.2 * rademacherSign eps w3.1 w3.2) with hF
  -- F eps equals the matrix-chaos inner product (definitional + bridge)
  have hFeq : ∀ eps, F eps = ⟪Matrix.toEuclideanLin
      (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
        (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
         else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
                * rademacherSign eps w3.1 w3.2) • a w1 w2 w3)) xv, yv⟫_ℝ := by
    intro eps; rw [hF, bridge eps]
  -- rewrite hmean, hvar in terms of F
  have hmeanF : rademacherExpectation F = 0 := by
    rw [show F = (fun eps => ⟪Matrix.toEuclideanLin
          (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
            (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
             else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
                    * rademacherSign eps w3.1 w3.2) • a w1 w2 w3)) xv, yv⟫_ℝ)
        from funext hFeq]
    exact hmean
  have hvarF : 0 < rademacherExpectation (fun ε => (F ε) ^ 2) := by
    rw [show (fun ε => (F ε)^2) = (fun eps => (⟪Matrix.toEuclideanLin
          (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
            (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
             else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
                    * rademacherSign eps w3.1 w3.2) • a w1 w2 w3)) xv, yv⟫_ℝ) ^ 2) from by
            funext eps; rw [hFeq eps]]
    exact hvar
  -- L4/L2 from 4f14a5e7 on acoef
  have hL4 : rademacherExpectation (fun ε => (F ε) ^ 4) ≤ 729 * (rademacherExpectation (fun ε => (F ε)^2))^2 :=
    rademacher_trilinear_chaos_l4_l2_bonami_hypercontractivity acoef
  -- Paley-Zygmund positivity with K = 729
  have hpz := rademacher_lower_tail_positivity_from_l4_l2_hypercontractivity (729 : ℝ) F
    (by norm_num) hmeanF hvarF hL4
  -- 1/(4*729) = 1/2916
  have h2916 : (1:ℝ) / (4 * 729) = 1 / 2916 := by norm_num
  rw [h2916] at hpz
  -- event monotonicity: {0 ≤ F} ⊆ {‖T‖ ≤ ‖T+M‖}
  refine le_trans hpz ?_
  unfold rademacherExpectation
  apply Finset.sum_le_sum
  intro eps _
  apply mul_le_mul_of_nonneg_left _ (by unfold rademacherObservationWeight; positivity)
  -- pointwise: indicator(0≤F eps) ≤ indicator(‖T‖ ≤ ‖T+M‖)
  simp only
  by_cases hFpos : 0 ≤ F eps
  · rw [if_pos hFpos]
    -- show ‖T‖ ≤ ‖T+M‖
    have hge : spectralNorm T ≤ spectralNorm (T +
        (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
          (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
           else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
                  * rademacherSign eps w3.1 w3.2) • a w1 w2 w3))) := by
      have hlb := spec_lb (T +
          (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
            (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
             else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
                    * rademacherSign eps w3.1 w3.2) • a w1 w2 w3))) xv yv hxv hyv
      -- ⟪(T+M)xv,yv⟫ = ⟪Txv,yv⟫ + ⟪Mxv,yv⟫ = ‖T‖ + F eps ≥ ‖T‖
      rw [map_add, LinearMap.add_apply, inner_add_left, hnorm, bridge eps] at hlb
      have : spectralNorm T ≤ spectralNorm T + F eps := by rw [hF]; linarith [hFpos]
      calc spectralNorm T ≤ spectralNorm T + F eps := this
        _ = spectralNorm T + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
              (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : ℝ)
               else acoef w1 w2 w3 * rademacherSign eps w1.1 w1.2
                      * rademacherSign eps w2.1 w2.2 * rademacherSign eps w3.1 w3.2)) := by rw [hF]
        _ ≤ _ := hlb
    rw [if_pos hge]
  · rw [if_neg hFpos]
    positivity
