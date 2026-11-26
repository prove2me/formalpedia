-- Prove2me | solution 1 for section5_lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:45:51.44542+00:00
-- url     : https://prove2.me/submissions/0d5ba76f-fb9f-4a88-a8ea-d8834243746b

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5DiscretizationLemma
import Definitions.Def_Section5Verified_Section5GridPhaseMatchesQEX
import Definitions.Def_Section5Verified_Section5PhysicalHermiteGrid
import Mathlib
import Theorems.Thm_section5_bit_coefficient_error_51
import Theorems.Thm_section5_bit_phase_state_eq_qex_phase
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Example QuantumLTF.Membership QuantumLTF.Membership.Supplement

/-! Lemma 5.1 for the exact QEX phase input and the public discrete Hermite kets. -/











theorem section5_flatten_phase_state {n q : ℕ} (w : EuclideanSpace ℝ (Fin n)) (hq : 0 < q) :
    section5_flatten_isometry n q (section5_bit_phase_state w q) = section5_qex_phase_input w q := by
  ext x
  obtain ⟨z,rfl⟩ := (section5_register_equiv n q).surjective x
  change section5_bit_phase_state w q ((section5_register_equiv n q).symm (section5_register_equiv n q z)) = _
  rw [Equiv.symm_apply_apply]
  exact section5_bit_phase_state_eq_qex_phase w hq z





end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership QuantumLTF.Membership.Supplement

theorem solution (n q D : ℕ) (hq : 0 < q) (hD : 1 ≤ D)
    (hsize : 64*(n:ℝ)^2*(D+1) ≤ (2:ℝ)^q) (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) :
    Real.sqrt (∑ a : Fin n → Fin D,
      ‖inner ℂ (section5_flat_hermite_tensor n q D a) (section5_qex_phase_input w q)-
        (hermCoeff w (fun i => (a i : ℕ)) : ℂ)‖^2) ≤
      24*n*Real.sqrt ((D+1)/(2:ℝ)^q)+2*(8*n/(2:ℝ)^q)^(1/4:ℝ)+
        2*Real.sqrt (2*n)*Real.exp (-Real.pi*(2:ℝ)^q/4) := by
  rw [← section5_flatten_phase_state w hq]
  simp only [section5_flat_hermite_tensor,(section5_flatten_isometry n q).inner_map_map]
  exact section5_bit_coefficient_error_51 n q D hq hD hsize w hw
