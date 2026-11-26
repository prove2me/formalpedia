-- Prove2me | solution 1 for section5_unnormalized_real_recovery
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:07:49.608847+00:00
-- url     : https://prove2.me/submissions/695e7945-60ed-4f8f-9ff0-0991b558acb5

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
import Definitions.Def_Section5Verified_Section5PhaseRecovery
import Definitions.Def_Section5Verified_Section5QuantizedReconstruction
import Mathlib
import Theorems.Thm_section5_real_direction_recovery
section
set_option autoImplicit false

/-! Passing from a powered matrix column to its larger real/imaginary part needs
no square root in the algorithm. Normalization is used only in the guarantee. -/

theorem section5_real_part_real_smul {n : ℕ} (c : ℝ) (y : EuclideanSpace ℂ (Fin n)) :
    section5_real_part (c • y)=c • section5_real_part y := by
  ext i
  simp [section5_real_part]

theorem section5_imag_part_real_smul {n : ℕ} (c : ℝ) (y : EuclideanSpace ℂ (Fin n)) :
    section5_imag_part (c • y)=c • section5_imag_part y := by
  ext i
  simp [section5_imag_part]

theorem section5_larger_real_part_pos_smul {n : ℕ} (c : ℝ) (hc : 0 < c)
    (y : EuclideanSpace ℂ (Fin n)) :
    section5_larger_real_part (c • y)=c • section5_larger_real_part y := by
  simp only [section5_larger_real_part,section5_real_part_real_smul,
    section5_imag_part_real_smul,norm_smul,Real.norm_of_nonneg hc.le,
    mul_le_mul_iff_right₀ hc]
  split_ifs <;> rfl

theorem section5_larger_real_part_normalize {n : ℕ} (y : EuclideanSpace ℂ (Fin n)) (hy : y ≠ 0) :
    section5_larger_real_part (NormedSpace.normalize y)=‖y‖⁻¹ • section5_larger_real_part y :=
  section5_larger_real_part_pos_smul _ (inv_pos.mpr (norm_pos_iff.mpr hy)) y





end
set_option autoImplicit false
theorem solution {n : ℕ}
    (y : EuclideanSpace ℂ (Fin n)) (hy : y ≠ 0)
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1)
    (ζ : ℂ) (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    (hclose : ‖NormedSpace.normalize y-ζ • section5_complexify w‖ ≤ ε/24) :
    section5_larger_real_part y ≠ 0 ∧
      (‖NormedSpace.normalize (section5_larger_real_part y)-w‖ ≤ ε/6 ∨
        ‖NormedSpace.normalize (section5_larger_real_part y)+w‖ ≤ ε/6) := by
  have hh := section5_real_direction_recovery (NormedSpace.normalize y) w ζ ε
    (NormedSpace.norm_normalize hy) hw hε hε' hclose
  change section5_larger_real_part (NormedSpace.normalize y) ≠ 0 ∧ _ at hh
  have hpart := section5_larger_real_part_normalize y hy
  rw [hpart] at hh
  have hr0 : section5_larger_real_part y ≠ 0 := by
    intro h
    exact hh.1 (by rw [h,smul_zero])
  refine ⟨hr0,?_⟩
  have hrec := hh.2
  change ‖NormedSpace.normalize (section5_larger_real_part (NormedSpace.normalize y))-w‖ ≤ ε/6 ∨
    ‖NormedSpace.normalize (section5_larger_real_part (NormedSpace.normalize y))+w‖ ≤ ε/6 at hrec
  have hnormalized : NormedSpace.normalize (section5_larger_real_part (NormedSpace.normalize y))=
      NormedSpace.normalize (section5_larger_real_part y) := by
    rw [hpart,NormedSpace.normalize_smul_of_pos (inv_pos.mpr (norm_pos_iff.mpr hy))]
  simpa only [hnormalized] using hrec
