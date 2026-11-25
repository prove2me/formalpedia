-- Prove2me | solution 1 for qnRuleTorus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:10:01.003581+00:00
-- url     : https://prove2.me/submissions/c49bcab1-f097-4095-bb98-dad83b0f9188

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_SecondHermitianPartDiagonal
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnRuleTorus
import Theorems.Thm_P2M_PI_QnRT_rdV_dz__4662447fe890
import Theorems.Thm_PI_QnRT_X1_eq
import Theorems.Thm_PI_QnRT_depthNumbers_threshold_eq
import Theorems.Thm_PI_QnRT_first_hermitian_part_diagonal
import Theorems.Thm_PI_QnRT_lin_single
import Theorems.Thm_PI_QnRT_second_hermitian_part_diagonal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : Formalism.FourierDecayAlt.Q.RuleTorus := by
  open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q PI.QnRT in
  intro E _ _ k r l D f hD hf c hc g₁ hg₁ hmem
  have hcl : c l ≠ 0 := hc l
  have h1 : -((1 / 2 : ℝ) : ℂ) = -star ((1 / 2 : ℝ) : ℂ) := by simp
  have h2 : ((-1 / 2 : ℝ) : ℂ) * Complex.I = -star (((-1 / 2 : ℝ) : ℂ) * Complex.I) := by
    simp
  have h3 : ((1 / 2 : ℝ) : ℂ) = -star (-((1 / 2 : ℝ) : ℂ)) := by simp
  set φ : (Fin r → ℂ) → E := fun c' => f (w1 k r l (c' l) * g₁) with hφ
  set L := fderiv ℝ φ c with hL
  refine ⟨?_, ?_⟩
  · simp only [EH, EabH]
    rw [X1_eq, depthNumbers_threshold_eq, rdV_dz' l D f hf c hcl g₁ hg₁ hmem _ _ h1,
      rdV_dz' l D f hf c hcl g₁ hg₁ hmem _ _ h2]
    simp only [pOp, wirt, if_pos hc]
    rw [lin_single l L (c l * ((1 / 2 : ℝ) : ℂ)), lin_single l L (c l * (((-1 / 2 : ℝ) : ℂ) * Complex.I))]
    generalize L (Pi.single l 1) = A
    generalize L (Pi.single l Complex.I) = B
    obtain ⟨a, b, hab⟩ : ∃ a b : ℝ, c l = (a : ℂ) + (b : ℂ) * Complex.I :=
      ⟨_, _, (Complex.re_add_im _).symm⟩
    rw [hab]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
    match_scalars <;> simp [Complex.ext_iff] <;> ring
  · simp only [EH, EabH]
    rw [first_hermitian_part_diagonal, second_hermitian_part_diagonal, rdV_dz' l D f hf c hcl g₁ hg₁ hmem _ _ h3,
      rdV_dz' l D f hf c hcl g₁ hg₁ hmem _ _ h2]
    simp only [pbOp, wirtBar, if_pos hc]
    rw [lin_single l L (c l * -((1 / 2 : ℝ) : ℂ)), lin_single l L (c l * (((-1 / 2 : ℝ) : ℂ) * Complex.I))]
    generalize L (Pi.single l 1) = A
    generalize L (Pi.single l Complex.I) = B
    obtain ⟨a, b, hab⟩ : ∃ a b : ℝ, c l = (a : ℂ) + (b : ℂ) * Complex.I :=
      ⟨_, _, (Complex.re_add_im _).symm⟩
    rw [hab]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
    match_scalars <;> simp [Complex.ext_iff] <;> ring
