-- Prove2me | solution 1 for schur_orthogonality_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:13:18.100111+00:00
-- url     : https://prove2.me/submissions/4ea76a94-aaa2-4247-889e-6e9eb5a5014d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhSchurConv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurConvolution_MapMulApply
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_PhSchurConv
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhSchurConv_Main_coef_conv
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhSchurConv_Main_coef_inv
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhSchurConv_Main_star_inner


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.PhSchurConv.SchurConv := by
  open MeasureTheory in
  open scoped InnerProductSpace in
  intro G _ _ _ _ _ _ μ _ _ _ Hσ _ _ σ d w hU hF hw
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hF.1)
  have hstard : star (d : ℂ) = d := Complex.conj_ofReal d
  have hinv : (d : ℂ) * (d : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hd
  have h1 : σ 1 = 1 := hU.1
  refine ⟨?_, ?_⟩
  · unfold PI.PhSchurConv.PhConv
    refine ⟨?_, ?_, ?_⟩
    · simp only [PI.PhSchurConv.coefM]
      rw [h1, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K, hw]
      simp
    · intro g
      simp only [PI.PhSchurConv.phOf, PI.PhSchurConv.coefM]
      rw [(PI.UnitaryGroupMassFormula.PhSchurConv.Main.coef_inv hU)]
      simp only [star_mul', star_star, hstard]
      try ring
    · intro x y
      have key : ∀ g, PI.PhSchurConv.phOf σ w d g * PI.PhSchurConv.phOf σ w d (x⁻¹ * g⁻¹ * y)
          = ((d : ℂ) * d) * (⟪σ y w, σ g (σ x w)⟫_ℂ * star ⟪w, σ g w⟫_ℂ) := by
        intro g
        simp only [PI.PhSchurConv.phOf, PI.PhSchurConv.coefM]
        rw [(PI.UnitaryGroupMassFormula.PhSchurConv.Main.coef_conv hU), PI.UnitaryGroupMassFormula.PhSchurConv.Main.star_inner (σ g (σ x w)) (σ y w)]
        ring
      obtain ⟨hi, he⟩ := hF.2 (σ x w) (σ y w) w w
      simp_rw [key]
      refine ⟨hi.const_mul _, ?_⟩
      rw [integral_const_mul, he]
      simp only [PI.PhSchurConv.phOf, PI.PhSchurConv.coefM]
      rw [PI.UnitaryGroupMassFormula.PhSchurConv.Main.star_inner w (σ y w), div_eq_mul_inv]
      linear_combination (⟪w, σ x w⟫_ℂ * ⟪σ y w, w⟫_ℂ * d) * hinv
  · intro u u'
    have key : ∀ g, PI.PhSchurConv.phOf σ w d g * ⟪u', σ g u⟫_ℂ
        = (d : ℂ) * (⟪u', σ g u⟫_ℂ * star ⟪w, σ g w⟫_ℂ) := by
      intro g
      simp only [PI.PhSchurConv.phOf, PI.PhSchurConv.coefM]
      ring
    obtain ⟨hi, he⟩ := hF.2 u u' w w
    simp_rw [key]
    refine ⟨hi.const_mul _, ?_⟩
    rw [integral_const_mul, he, div_eq_mul_inv]
    linear_combination (⟪w, u⟫_ℂ * ⟪u', w⟫_ℂ) * hinv
