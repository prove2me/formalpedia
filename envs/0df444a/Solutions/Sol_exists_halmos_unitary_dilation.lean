-- Prove2me | solution 1 for exists_halmos_unitary_dilation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:29:55.072331+00:00
-- url     : https://prove2.me/submissions/d8c41177-6581-49e6-9284-05c7d6279282

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Definitions.Def_Operator_Dilation_Halmos
section
open ContinuousLinearMap
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
@[simp]
private theorem halmosOffDiagonal_apply (T : E →L[ℂ] E)
    (x : WithLp 2 (E × E)) :
    halmosOffDiagonal T x = WithLp.toLp 2 (T x.snd, adjoint T x.fst) :=
  rfl
private theorem norm_halmosOffDiagonal_le (T : E →L[ℂ] E) :
    ‖halmosOffDiagonal T‖ ≤ ‖T‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg T) (halmosOffDiagonalLinear_bound T)
private theorem isSelfAdjoint_halmosOffDiagonal (T : E →L[ℂ] E) :
    IsSelfAdjoint (halmosOffDiagonal T) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  change ⟪halmosOffDiagonal T x, y⟫_ℂ = ⟪x, halmosOffDiagonal T y⟫_ℂ
  rw [halmosOffDiagonal_apply, halmosOffDiagonal_apply]
  simp only [WithLp.prod_inner_apply]
  simp only [adjoint_inner_right, adjoint_inner_left, add_comm]
  rfl
omit [CompleteSpace E] in
@[simp]
private theorem halmosGrading_apply (x : WithLp 2 (E × E)) :
    halmosGrading x = WithLp.toLp 2 (x.fst, -x.snd) :=
  rfl
private theorem one_sub_halmosOffDiagonal_sq_commute_grading (T : E →L[ℂ] E) :
    Commute (1 - halmosOffDiagonal T ^ 2) (halmosGrading (E := E)) := by
  rw [Commute]
  apply ContinuousLinearMap.ext
  intro x
  simp only [mul_apply_eq_comp, pow_two, sub_apply, one_apply_eq_self,
    halmosGrading_apply, halmosOffDiagonal_apply, WithLp.toLp_fst,
    WithLp.toLp_snd, map_neg]
  apply WithLp.ofLp_injective 2
  change (x.fst - T (adjoint T x.fst), -x.snd - -(adjoint T (T x.snd))) =
    (x.fst - T (adjoint T x.fst), -(x.snd - adjoint T (T x.snd)))
  apply Prod.ext
  · rfl
  · abel_nf
private theorem sqrt_one_sub_halmosOffDiagonal_sq_fst_zero (T : E →L[ℂ] E)
    (x : E) :
    ((CFC.sqrt (1 - halmosOffDiagonal T ^ 2) :
      WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E))
        (WithLp.toLp 2 (0, x))).fst = 0 := by
  have hcomm : Commute (CFC.sqrt (1 - halmosOffDiagonal T ^ 2))
      (halmosGrading (E := E)) := by
    simpa only [CFC.sqrt] using
      (one_sub_halmosOffDiagonal_sq_commute_grading T).cfcₙ_nnreal NNReal.sqrt
  have happ := congrArg
    (fun q : WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E) =>
      (q (WithLp.toLp 2 (0, x))).fst) hcomm.eq
  simp only [mul_apply_eq_comp, halmosGrading_apply, WithLp.toLp_fst,
    WithLp.toLp_snd] at happ
  have hneg : WithLp.toLp 2 ((0 : E), -x) =
      -(WithLp.toLp 2 ((0 : E), x) : WithLp 2 (E × E)) := by
    rw [← WithLp.toLp_neg]
    congr 1
    apply Prod.ext
    · exact (neg_zero : -(0 : E) = 0).symm
    · rfl
  rw [hneg, map_neg, WithLp.neg_fst] at happ
  let v : E := ((CFC.sqrt (1 - halmosOffDiagonal T ^ 2) :
    WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E))
      (WithLp.toLp 2 (0, x))).fst
  change -v = v at happ
  have hvadd : v + v = 0 := by
    calc
      v + v = -v + v := by rw [happ]
      _ = 0 := neg_add_cancel v
  have htwo : (2 : ℂ) • v = 0 := by
    simpa only [two_smul] using hvadd
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
omit [CompleteSpace E] in
@[simp]
private theorem halmosFlip_apply (x : WithLp 2 (E × E)) :
    halmosFlip x = WithLp.toLp 2 (x.snd, x.fst) :=
  rfl
private theorem halmosFlip_mem_unitary :
    halmosFlip (E := E) ∈ unitary (WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E)) := by
  exact (Unitary.linearIsometryEquiv.symm
    (LinearIsometryEquiv.withLpProdComm 2 ℂ E E)).property
end

set_option autoImplicit false
open ContinuousLinearMap
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1) :
    ∃ (U : WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E)),
    U ∈ unitary (WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E)) ∧
    ∀ x : E, (U (WithLp.toLp 2 (x, 0))).fst = T x := by
  let a := halmosOffDiagonal T
  let w := a + Complex.I • CFC.sqrt (1 - a ^ 2)
  let U := w * halmosFlip (E := E)
  have ha : IsSelfAdjoint a := isSelfAdjoint_halmosOffDiagonal T
  have haw : ‖a‖ ≤ 1 := (norm_halmosOffDiagonal_le T).trans hT
  have hw : w ∈ unitary (WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E)) :=
    ha.self_add_I_smul_cfcSqrt_sub_sq_mem_unitary a haw
  refine ⟨U, ?_, ?_⟩
  · exact (unitary _).mul_mem hw halmosFlip_mem_unitary
  · intro x
    simp only [U, w, a, mul_apply_eq_comp, halmosFlip_apply, WithLp.toLp_fst,
      WithLp.toLp_snd, add_apply, halmosOffDiagonal_apply, smul_apply,
      WithLp.add_fst, WithLp.smul_fst, map_zero]
    rw [sqrt_one_sub_halmosOffDiagonal_sq_fst_zero]
    simp only [add_zero, smul_zero]
