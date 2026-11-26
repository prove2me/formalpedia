-- Prove2me | solution 1 for section5_qex_phase_disagreement
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:59:20.246672+00:00
-- url     : https://prove2.me/submissions/b7c3590c-44d3-444e-a0ca-6a32b2e55871

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
import Definitions.Def_Section5Verified_Section5ExamplePhase
import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership
theorem solution {n q : ℕ} (w u : EuclideanSpace ℝ (Fin n)) :
    ‖section5_qex_phase_input w q-section5_qex_phase_input u q‖^2 =
      4*∑ z : Qubits (n*q),
        if ltf w 0 (gridPoint z) ≠ ltf u 0 (gridPoint z) then
          gridWeight z/(∑ x : Qubits (n*q), gridWeight x) else 0 := by
  classical
  have hZ : 0 < ∑ x : Qubits (n*q), gridWeight x :=
    Finset.sum_pos (fun x _ => Real.exp_pos _) Finset.univ_nonempty
  rw [EuclideanSpace.norm_sq_eq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  have hphase : (section5_qex_phase_input w q-section5_qex_phase_input u q) z =
      ((ltf w 0 (gridPoint z):ℂ)-(ltf u 0 (gridPoint z):ℂ))*section5_grid_amplitude z := by
    change (ltf w 0 (gridPoint z):ℂ)*section5_grid_amplitude z-
      (ltf u 0 (gridPoint z):ℂ)*section5_grid_amplitude z = _
    ring
  have hlabel : ‖(ltf w 0 (gridPoint z):ℂ)-(ltf u 0 (gridPoint z):ℂ)‖^2 =
      if ltf w 0 (gridPoint z) ≠ ltf u 0 (gridPoint z) then 4 else 0 := by
    unfold ltf sgn
    split_ifs <;> norm_num at *
  rw [hphase,norm_mul,mul_pow,hlabel]
  have hweight : 0 ≤ gridWeight z := (Real.exp_pos _).le
  have hsqrt : (Real.sqrt (gridWeight z/(∑ x : Qubits (n*q), gridWeight x)))^2 =
      gridWeight z/(∑ x : Qubits (n*q), gridWeight x) :=
    Real.sq_sqrt (div_nonneg hweight hZ.le)
  simp only [section5_grid_amplitude,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    hsqrt]
  split_ifs <;> ring
