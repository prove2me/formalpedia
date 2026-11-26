-- Prove2me | solution 1 for section5_normalized_phase_sum_eq_qex
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:16:36.865549+00:00
-- url     : https://prove2.me/submissions/e503cbc1-f084-46b1-9698-3c6c18b87757

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5DiscretizationLemma
import Definitions.Def_Section5Verified_Section5PhaseStateError
import Mathlib
import Theorems.Thm_section5_normalized_phase_distance_eq_qex
import Theorems.Thm_section5_phase_amplitude_norm
import Theorems.Thm_section5_sampled_phase_toLp_ne_zero
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Example QuantumLTF.Membership QuantumLTF.Membership.Supplement

/-! Lemma 5.1 for the exact QEX phase input and the public discrete Hermite kets. -/









theorem section5_qex_phase_input_norm {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (q : ℕ) :
    ‖section5_qex_phase_input w q‖=1 := section5_phase_amplitude_norm w







end
set_option autoImplicit false
open MeasureTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership
theorem solution {n q : ℕ} (w u : EuclideanSpace ℝ (Fin n))
    (hq : 0 < q) :
    ‖NormedSpace.normalize ((section5_sampled_phase_memLp w (2^q) (Nat.two_pow_pos q)).toLp
        (section5_sampled_phase_state w (2^q)))+
      NormedSpace.normalize ((section5_sampled_phase_memLp u (2^q) (Nat.two_pow_pos q)).toLp
        (section5_sampled_phase_state u (2^q)))‖ =
      ‖section5_qex_phase_input w q+section5_qex_phase_input u q‖ := by
  let A := NormedSpace.normalize ((section5_sampled_phase_memLp w (2^q) (Nat.two_pow_pos q)).toLp
    (section5_sampled_phase_state w (2^q)))
  let B := NormedSpace.normalize ((section5_sampled_phase_memLp u (2^q) (Nat.two_pow_pos q)).toLp
    (section5_sampled_phase_state u (2^q)))
  have hA : ‖A‖=1 := NormedSpace.norm_normalize (section5_sampled_phase_toLp_ne_zero w (2^q) (Nat.two_pow_pos q))
  have hB : ‖B‖=1 := NormedSpace.norm_normalize (section5_sampled_phase_toLp_ne_zero u (2^q) (Nat.two_pow_pos q))
  have hp := parallelogram_law_with_norm ℂ A B
  have hp' := parallelogram_law_with_norm ℂ (section5_qex_phase_input w q) (section5_qex_phase_input u q)
  rw [hA,hB] at hp
  rw [section5_qex_phase_input_norm,section5_qex_phase_input_norm] at hp'
  have hd : ‖A-B‖=‖section5_qex_phase_input w q-section5_qex_phase_input u q‖ :=
    section5_normalized_phase_distance_eq_qex w u hq
  rw [hd] at hp
  change ‖A+B‖=‖section5_qex_phase_input w q+section5_qex_phase_input u q‖
  nlinarith [norm_nonneg (A+B),norm_nonneg (section5_qex_phase_input w q+section5_qex_phase_input u q)]
