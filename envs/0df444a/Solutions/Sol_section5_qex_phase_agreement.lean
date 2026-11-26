-- Prove2me | solution 1 for section5_qex_phase_agreement
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:04:10.851331+00:00
-- url     : https://prove2.me/submissions/d373d662-36ee-4b73-a8b2-9f72d72f0263

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
import Mathlib
import Theorems.Thm_section5_phase_amplitude_norm
import Theorems.Thm_section5_qex_phase_disagreement
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Example QuantumLTF.Membership QuantumLTF.Membership.Supplement

/-! Lemma 5.1 for the exact QEX phase input and the public discrete Hermite kets. -/









theorem section5_qex_phase_input_norm {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (q : ℕ) :
    ‖section5_qex_phase_input w q‖=1 := section5_phase_amplitude_norm w







end
set_option autoImplicit false
open MeasureTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership
theorem solution {n q : ℕ} (w u : EuclideanSpace ℝ (Fin n)) :
    ‖section5_qex_phase_input w q+section5_qex_phase_input u q‖^2 =
      4*∑ z : Qubits (n*q),
        if ltf w 0 (gridPoint z) = ltf u 0 (gridPoint z) then
          gridWeight z/(∑ x : Qubits (n*q), gridWeight x) else 0 := by
  classical
  have hZ : 0 < ∑ x : Qubits (n*q), gridWeight x :=
    Finset.sum_pos (fun x _ => Real.exp_pos _) Finset.univ_nonempty
  have htotal : (∑ z : Qubits (n*q), gridWeight z/(∑ x : Qubits (n*q), gridWeight x))=1 := by
    rw [← Finset.sum_div,div_self hZ.ne']
  have he := section5_qex_phase_disagreement (q := q) w u
  have hp := parallelogram_law_with_norm ℂ (section5_qex_phase_input w q) (section5_qex_phase_input u q)
  rw [section5_qex_phase_input_norm,section5_qex_phase_input_norm] at hp
  have hparts : (∑ z : Qubits (n*q),
      if ltf w 0 (gridPoint z) = ltf u 0 (gridPoint z) then
        gridWeight z/(∑ x : Qubits (n*q), gridWeight x) else 0)+
      (∑ z : Qubits (n*q),
      if ltf w 0 (gridPoint z) ≠ ltf u 0 (gridPoint z) then
        gridWeight z/(∑ x : Qubits (n*q), gridWeight x) else 0)=1 := by
    rw [← Finset.sum_add_distrib]
    convert htotal using 1
    apply Finset.sum_congr rfl
    intro z hz
    by_cases h : ltf w 0 (gridPoint z) = ltf u 0 (gridPoint z) <;> simp [h]
  nlinarith
