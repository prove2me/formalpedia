-- Prove2me | solution 1 for section5_qex_negative_orientation_vote_quarter
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:35:39.906496+00:00
-- url     : https://prove2.me/submissions/99ae5a17-26b8-40ea-ac79-855e091a99d2

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
import Theorems.Thm_section5_gaussian_disagreement_proved
import Theorems.Thm_section5_ideal_phase_distance_sq
import Theorems.Thm_section5_ideal_phase_neg
import Theorems.Thm_section5_normalized_phase_sum_eq_qex
import Theorems.Thm_section5_orientation_phase_error_small
import Theorems.Thm_section5_qex_phase_agreement
section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership

/-! Orientation testing as an exact squared distance of phase states. -/





theorem section5_close_ideal_phase_distance {n : ℕ} (w u : EuclideanSpace ℝ (Fin n))
    (hw : ‖w‖=1) (hu : ‖u‖=1) (hclose : ‖w-u‖ ≤ 1/6) :
    ‖(section5_ideal_phase_memLp w).toLp (section5_ideal_phase_state w)-
      (section5_ideal_phase_memLp u).toLp (section5_ideal_phase_state u)‖ ≤ 2/3 := by
  have h := (section5_gaussian_disagreement_proved w u hw hu 0 0).1
  simp only [sub_self,abs_zero,zero_div,add_zero] at h
  have hsq := section5_ideal_phase_distance_sq w u
  nlinarith [norm_nonneg ((section5_ideal_phase_memLp w).toLp (section5_ideal_phase_state w)-
    (section5_ideal_phase_memLp u).toLp (section5_ideal_phase_state u))]



end
set_option autoImplicit false
open MeasureTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership
theorem solution (n q : ℕ) (hn : 1 ≤ n) (hq : 0 < q)
    (hgrid : 1073741824*(n:ℝ)^2 ≤ (2:ℝ)^q)
    (w u : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) (hu : ‖u‖=1) (hclose : ‖w+u‖ ≤ 1/6) :
    (∑ z : Qubits (n*q),
      if ltf w 0 (gridPoint z) = ltf u 0 (gridPoint z) then
        gridWeight z/(∑ x : Qubits (n*q), gridWeight x) else 0) ≤ 1/4 := by
  have hgrid' : 1073741824*(n:ℝ)^2 ≤ ((2^q:ℕ):ℝ) := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hgrid
  let ψw := NormedSpace.normalize ((section5_sampled_phase_memLp w (2^q) (Nat.two_pow_pos q)).toLp
    (section5_sampled_phase_state w (2^q)))
  let ψu := NormedSpace.normalize ((section5_sampled_phase_memLp u (2^q) (Nat.two_pow_pos q)).toLp
    (section5_sampled_phase_state u (2^q)))
  let φw := (section5_ideal_phase_memLp w).toLp (section5_ideal_phase_state w)
  let φu := (section5_ideal_phase_memLp u).toLp (section5_ideal_phase_state u)
  have hwerror : ‖ψw-φw‖ ≤ 1/6 := section5_orientation_phase_error_small n (2^q) hn
    (Nat.two_pow_pos q) hgrid' w hw
  have huerror : ‖ψu-φu‖ ≤ 1/6 := section5_orientation_phase_error_small n (2^q) hn
    (Nat.two_pow_pos q) hgrid' u hu
  have hideal : ‖φw+φu‖ ≤ 2/3 := by
    have hh := section5_close_ideal_phase_distance w (-u) hw (by simpa using hu)
      (by simpa only [sub_neg_eq_add] using hclose)
    rwa [section5_ideal_phase_neg u hu,sub_neg_eq_add] at hh
  have hnorm : ‖ψw+ψu‖ ≤ 1 := by
    have heq : ψw+ψu=(ψw-φw)+(φw+φu)+(ψu-φu) := by abel
    rw [heq]
    calc
      _ ≤ ‖(ψw-φw)+(φw+φu)‖+‖ψu-φu‖ := norm_add_le _ _
      _ ≤ (‖ψw-φw‖+‖φw+φu‖)+‖ψu-φu‖ := add_le_add (norm_add_le _ _) (le_refl _)
      _ ≤ 1 := by linarith
  have hnorm' : ‖section5_qex_phase_input w q+section5_qex_phase_input u q‖ ≤ 1 := by
    rw [← section5_normalized_phase_sum_eq_qex w u hq]
    exact hnorm
  have heq := section5_qex_phase_agreement (q := q) w u
  nlinarith [sq_nonneg (‖section5_qex_phase_input w q+section5_qex_phase_input u q‖-1),
    norm_nonneg (section5_qex_phase_input w q+section5_qex_phase_input u q)]
