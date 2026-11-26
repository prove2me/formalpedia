-- Prove2me | solution 1 for section5_orientation_born_success
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T21:11:02.620166+00:00
-- url     : https://prove2.me/submissions/cf2a2621-ab22-4d80-bc6c-c4f04d084770

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
import Definitions.Def_QuantumLTF_Membership_Supplement_probMixed
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
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5OrientationDecision
import Definitions.Def_Section5Verified_Section5ThreeQEXMeasurement
import Mathlib
import Theorems.Thm_section5_raw_orientation_success
import Theorems.Thm_section5_three_qex_input_postprocess_probability
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership
open Classical in
theorem solution {α : Type*} [Fintype α] [DecidableEq α]
    (n q : ℕ) (hn : 1 ≤ n) (hgrid : (2:ℝ)^40*(n:ℝ)^2 ≤ (2:ℝ)^q)
    (w r : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) (hr : r ≠ 0)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) (flip : Bool)
    (hclose : ‖(if flip then -NormedSpace.normalize r else NormedSpace.normalize r)-w‖ ≤ ε/6)
    (a : α)
    (U : Matrix (α × (Qubits (n*q+1) × Qubits (n*q+1) × Qubits (n*q+1)))
      (α × (Qubits (n*q+1) × Qubits (n*q+1) × Qubits (n*q+1))) ℂ)
    (F : Equiv.Perm (α × (Qubits (n*q+1) × Qubits (n*q+1) × Qubits (n*q+1))))
    (hact : ∀ z, act U (ket z)=ket (F z))
    (readout : α × (Qubits (n*q+1) × Qubits (n*q+1) × Qubits (n*q+1)) → EuclideanSpace ℝ (Fin n))
    (hread : ∀ x, readout (F (a,section5_labelled_three_qex_outcome w x))=
      section5_oriented_direction w r x) :
    probEvent (act U (tensorVec (ket a) (section5_three_qex_state (q:=q) w)))
      (fun z => readout z ≠ 0 ∧ ‖NormedSpace.normalize (readout z)-w‖ ≤ ε) ≥ 27/32 := by
  rw [section5_three_qex_input_postprocess_probability w a U F hact]
  simp only [hread]
  exact section5_raw_orientation_success n q hn hgrid w r hw hr ε hε hε' flip hclose
