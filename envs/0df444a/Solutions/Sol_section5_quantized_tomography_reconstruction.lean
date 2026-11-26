-- Prove2me | solution 1 for section5_quantized_tomography_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:13:17.39989+00:00
-- url     : https://prove2.me/submissions/7cb7650d-036c-4365-81c8-d46005b5aec9

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5FixedPointQuantization
import Definitions.Def_Section5Verified_Section5PhaseRecovery
import Definitions.Def_Section5Verified_Section5QuantizedReconstruction
import Mathlib
import Theorems.Thm_section5_quantize_normalized_error
import Theorems.Thm_section5_real_direction_recovery
import Theorems.Thm_section5_spectral_estimator_exists
section
set_option autoImplicit false







theorem section5_parts_norm_sq {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) :
    ‖section5_real_part v‖^2 + ‖section5_imag_part v‖^2 = ‖v‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq, section5_real_part, section5_imag_part,
    WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem section5_real_part_contraction {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) :
    ‖section5_real_part v‖ ≤ ‖v‖ := by
  have hh : ‖section5_real_part v‖^2 ≤ ‖v‖^2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i hi
    change ‖(v i).re‖^2 ≤ ‖v i‖^2
    rw [Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2
  nlinarith [norm_nonneg (section5_real_part v), norm_nonneg v]

theorem section5_imag_part_contraction {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) :
    ‖section5_imag_part v‖ ≤ ‖v‖ := by
  have hh : ‖section5_imag_part v‖^2 ≤ ‖v‖^2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i hi
    change ‖(v i).im‖^2 ≤ ‖v i‖^2
    rw [Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm _) 2
  nlinarith [norm_nonneg (section5_imag_part v), norm_nonneg v]



end
section
set_option autoImplicit false

open ContinuousLinearMap InnerProductSpace

/-! Operator-norm accuracy gives an explicit finite-bit real output, up to sign.
The spectral choice here is still noncomputable; this does not certify the runtime
of a classical spectral algorithm or construct the tomography measurement. -/



theorem section5_larger_real_part_norm {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) (hv : ‖v‖=1) :
    2/3 < ‖section5_larger_real_part v‖ ∧ ‖section5_larger_real_part v‖ ≤ 1 := by
  have hparts : ‖section5_real_part v‖^2+‖section5_imag_part v‖^2=1 := by
    rw [section5_parts_norm_sq,hv,one_pow]
  unfold section5_larger_real_part
  split_ifs with h
  · exact ⟨by nlinarith [norm_nonneg (section5_real_part v),norm_nonneg (section5_imag_part v)],
      (section5_real_part_contraction v).trans_eq hv⟩
  · exact ⟨by nlinarith [norm_nonneg (section5_real_part v),norm_nonneg (section5_imag_part v)],
      (section5_imag_part_contraction v).trans_eq hv⟩



end
section
set_option autoImplicit false

open ContinuousLinearMap InnerProductSpace

/-! Statistical operator error implies the real, sign-ambiguous direction guarantee
used by Theorem 5.6. This is the reconstruction guarantee; no efficient measurement
or classical eigenvector algorithm is assumed to have been constructed here. -/

theorem section5_complexify_norm {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) :
    ‖section5_complexify w‖=‖w‖ := by
  have hs : ‖section5_complexify w‖^2=‖w‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq,section5_complexify,WithLp.ofLp_toLp,
      Complex.norm_real]
  nlinarith [norm_nonneg w,norm_nonneg (section5_complexify w)]



end
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace
theorem solution (n : ℕ) (hn : 1 ≤ n)
    (L : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hL : IsSelfAdjoint L) :
    ∃ v : EuclideanSpace ℂ (Fin n), ‖v‖=1 ∧
      ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖=1 →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ f : ℕ, 128*(n:ℝ)/ε ≤ (2:ℝ)^f →
      ‖L-rankOne ℂ (section5_complexify w) (section5_complexify w)‖ ≤ ε/192 →
        let r := section5_quantize_vector f (section5_larger_real_part v)
        r ≠ 0 ∧ (‖NormedSpace.normalize r-w‖ ≤ ε/6 ∨ ‖NormedSpace.normalize r+w‖ ≤ ε/6) := by
  haveI : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  obtain ⟨v,hv,hrecover⟩ := section5_spectral_estimator_exists L hL
  refine ⟨v,hv,?_⟩
  intro w hw ε hε hε' f hprec herror
  obtain ⟨ζ,hζ,hclose⟩ := hrecover (section5_complexify w)
    (by rwa [section5_complexify_norm]) (ε/192) (by positivity) (by linarith) herror
  have hh := section5_real_direction_recovery v w ζ (ε/2) hv hw (by positivity) (by linarith)
    (by linarith)
  change section5_larger_real_part v ≠ 0 ∧
    (‖NormedSpace.normalize (section5_larger_real_part v)-w‖ ≤ (ε/2)/6 ∨
      ‖NormedSpace.normalize (section5_larger_real_part v)+w‖ ≤ (ε/2)/6) at hh
  let r := section5_larger_real_part v
  have hrnorm := section5_larger_real_part_norm v hv
  have hrcoord (i : Fin n) : |r i| ≤ 1 := by
    have hh := PiLp.norm_apply_le r i
    rw [Real.norm_eq_abs] at hh
    exact hh.trans hrnorm.2
  obtain ⟨hq0,hqclose⟩ := section5_quantize_normalized_error hn f ε hε hε' hprec r hrcoord hrnorm.1.le
  refine ⟨hq0,?_⟩
  rcases hh.2 with hminus | hplus
  · left
    have htri := norm_add_le
      (NormedSpace.normalize (section5_quantize_vector f r)-NormedSpace.normalize r)
      (NormedSpace.normalize r-w)
    have hid : (NormedSpace.normalize (section5_quantize_vector f r)-NormedSpace.normalize r)+
        (NormedSpace.normalize r-w)=NormedSpace.normalize (section5_quantize_vector f r)-w := by abel
    rw [hid] at htri
    dsimp only [r] at htri hqclose
    linarith
  · right
    have htri := norm_add_le
      (NormedSpace.normalize (section5_quantize_vector f r)-NormedSpace.normalize r)
      (NormedSpace.normalize r+w)
    have hid : (NormedSpace.normalize (section5_quantize_vector f r)-NormedSpace.normalize r)+
        (NormedSpace.normalize r+w)=NormedSpace.normalize (section5_quantize_vector f r)+w := by abel
    rw [hid] at htri
    dsimp only [r] at htri hqclose
    linarith
