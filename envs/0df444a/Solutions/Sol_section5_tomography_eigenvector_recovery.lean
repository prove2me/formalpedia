-- Prove2me | solution 1 for section5_tomography_eigenvector_recovery
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:01:45.559711+00:00
-- url     : https://prove2.me/submissions/4835a28f-0002-4682-83d5-0b9db49b8fb5

import Mathlib
import Theorems.Thm_section5_normalize_perturbation
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace
theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (L : E →L[ℂ] E) (w v : E)
    (hw : ‖w‖=1) (hv : ‖v‖=1) (η lam : ℝ) (hη : 0 ≤ η) (hη' : η < 1/4)
    (hlam : 1/2 ≤ lam) (herror : ‖L-rankOne ℂ w w‖ ≤ η)
    (heigen : L v=(lam:ℂ) • v) :
    ∃ ζ : ℂ, ‖ζ‖=1 ∧ ‖v-ζ • w‖ ≤ 4*η := by
  let c : ℂ := (lam:ℂ)⁻¹*inner ℂ w v
  have hlam0 : 0 < lam := by linarith
  have hlamc : (lam:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hlam0)
  have hrel : c • w-v=(lam:ℂ)⁻¹ • ((rankOne ℂ w w-L) v) := by
    simp only [c,sub_apply,rankOne_apply,heigen,smul_sub,smul_smul,
      inv_mul_cancel₀ hlamc,one_smul]
  have hdist : ‖c • w-v‖ ≤ 2*η := by
    rw [hrel,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hlam0]
    have hE : ‖(rankOne ℂ w w-L) v‖ ≤ η := by
      calc
        _ ≤ ‖rankOne ℂ w w-L‖*‖v‖ := (rankOne ℂ w w-L).le_opNorm v
        _ ≤ η := by simpa only [norm_sub_rev,hv,mul_one] using herror
    calc
      _ ≤ lam⁻¹*η := mul_le_mul_of_nonneg_left hE (inv_nonneg.mpr hlam0.le)
      _ ≤ 2*η := by
        have hi : lam⁻¹ ≤ 2 := by
          exact (inv_le_iff_one_le_mul₀' hlam0).mpr (by linarith)
        exact mul_le_mul_of_nonneg_right hi hη
  have hr : c • w ≠ 0 := by
    intro hz
    rw [hz,zero_sub,norm_neg,hv] at hdist
    linarith
  have hc : c ≠ 0 := by intro hz; exact hr (by rw [hz,zero_smul])
  have hv0 : v ≠ 0 := by intro hz; rw [hz,norm_zero] at hv; norm_num at hv
  let ζ : ℂ := ‖c‖⁻¹ • c
  have hζ : ‖ζ‖=1 := NormedSpace.norm_normalize hc
  have hnorm : NormedSpace.normalize (c • w)=ζ • w := by
    unfold NormedSpace.normalize
    rw [norm_smul,hw,mul_one]
    exact (smul_assoc _ _ _).symm
  have hpert := section5_normalize_perturbation (c • w) v hr hv0
  rw [hnorm,NormedSpace.normalize_eq_self_of_norm_eq_one hv,hv,div_one,norm_sub_rev] at hpert
  exact ⟨ζ,hζ,hpert.trans (by linarith)⟩
