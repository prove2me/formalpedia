-- Prove2me | solution 1 for section5_majority_decision_correct
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:55:51.07831+00:00
-- url     : https://prove2.me/submissions/ae6f8f38-19a6-41f2-b964-57ad2efa6d97

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
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5OrientationDecision
import Definitions.Def_Section5Verified_Section5QuantizedOrientation
import Mathlib
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership
theorem solution {n q : ℕ} (w u : EuclideanSpace ℝ (Fin n))
    (flip : Bool) (z : Qubits (n*q) × Qubits (n*q) × Qubits (n*q))
    (h : ¬ section5_quantized_majority_error w u flip z) :
    section5_oriented_direction w u z=(if flip then -u else u) := by
  by_cases ha : ltf w 0 (gridPoint z.1)=ltf u 0 (section5_bounded_window_vector q (gridPoint z.1)) <;>
  by_cases hb : ltf w 0 (gridPoint z.2.1)=ltf u 0 (section5_bounded_window_vector q (gridPoint z.2.1)) <;>
  by_cases hc : ltf w 0 (gridPoint z.2.2)=ltf u 0 (section5_bounded_window_vector q (gridPoint z.2.2)) <;>
  cases flip <;>
    simp [section5_quantized_majority_error,section5_quantized_orientation_error,
      section5_oriented_direction,section5_majority_bit,section5_quantized_vote,ha,hb,hc] at h ⊢
