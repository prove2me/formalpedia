-- Prove2me | solution 1 for section5_tomography_deflated_norm
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:07:26.360474+00:00
-- url     : https://prove2.me/submissions/18b25ffd-1d9c-4c52-a3d4-9ddcc9221b82

import Mathlib
import Theorems.Thm_section5_tomography_eigenvector_recovery
section
set_option autoImplicit false

open ContinuousLinearMap InnerProductSpace

/-! Quantitative deflation of a nearly pure spectral estimate. -/

theorem section5_rankOne_phase_invariant {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (w : E) (ζ : ℂ) (hζ : ‖ζ‖=1) :
    rankOne ℂ (ζ • w) (ζ • w)=rankOne ℂ w w := by
  have hh : (starRingEnd ℂ) ζ*ζ=1 := by
    rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq,hζ]
    norm_num
  ext x
  simp only [rankOne_apply,inner_smul_left,smul_smul]
  rw [mul_right_comm ((starRingEnd ℂ) ζ),hh,one_mul]

theorem section5_rankOne_unit_difference {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (v u : E) (hv : ‖v‖=1) (hu : ‖u‖=1) :
    ‖rankOne ℂ v v-rankOne ℂ u u‖ ≤ 2*‖v-u‖ := by
  have hid : rankOne ℂ v v-rankOne ℂ u u=
      rankOne ℂ (v-u) v+rankOne ℂ u (v-u) := by
    ext x
    simp only [sub_apply,add_apply,rankOne_apply,inner_sub_left,sub_smul,smul_sub]
    abel
  rw [hid]
  exact (norm_add_le _ _).trans_eq (by simp only [norm_rankOne,hv,hu,mul_one,one_mul]; ring)













end
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace
theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (L : E →L[ℂ] E) (w v : E)
    (hw : ‖w‖=1) (hv : ‖v‖=1) (η lam : ℝ) (hη : 0 ≤ η) (hη' : η < 1/4)
    (hlam : 1/2 ≤ lam) (hlow : 1-η ≤ lam)
    (herror : ‖L-rankOne ℂ w w‖ ≤ η) (heigen : L v=(lam:ℂ) • v) :
    ‖L-(lam:ℂ) • rankOne ℂ v v‖ ≤ 10*η := by
  obtain ⟨ζ,hζ,hclose⟩ := section5_tomography_eigenvector_recovery L w v hw hv η lam
    hη hη' hlam herror heigen
  have hL : ‖L‖ ≤ 1+η := by
    have hh := norm_sub_le L (rankOne ℂ w w)
    have ht := norm_add_le (L-rankOne ℂ w w) (rankOne ℂ w w)
    rw [sub_add_cancel] at ht
    simp only [norm_rankOne,hw,one_mul] at ht
    linarith
  have hlampos : 0 < lam := by linarith
  have hlamup : lam ≤ 1+η := by
    have hh := L.le_opNorm v
    rw [heigen,norm_smul,hv,mul_one,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hlampos] at hh
    exact hh.trans hL
  have hlamerr : |1-lam| ≤ η := abs_le.mpr ⟨by linarith,by linarith⟩
  have hproj : ‖rankOne ℂ w w-rankOne ℂ v v‖ ≤ 8*η := by
    have hu : ‖ζ • w‖=1 := by simp [norm_smul,hζ,hw]
    have hh := section5_rankOne_unit_difference v (ζ • w) hv hu
    rw [section5_rankOne_phase_invariant w ζ hζ,norm_sub_rev] at hh
    exact hh.trans (by linarith)
  have hid : L-(lam:ℂ) • rankOne ℂ v v=
      (L-rankOne ℂ w w)+(rankOne ℂ w w-rankOne ℂ v v)+
        ((1-lam:ℝ):ℂ) • rankOne ℂ v v := by
    push_cast
    simp only [sub_smul,one_smul]
    abel
  rw [hid]
  have hlast : ‖((1-lam:ℝ):ℂ) • rankOne ℂ v v‖ ≤ η := by
    simpa only [norm_smul,norm_rankOne,hv,mul_one,Complex.norm_real,Real.norm_eq_abs] using hlamerr
  exact (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) hlast).trans (by linarith))
