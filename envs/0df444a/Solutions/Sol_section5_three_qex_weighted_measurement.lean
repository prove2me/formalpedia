-- Prove2me | solution 1 for section5_three_qex_weighted_measurement
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:01:01.966477+00:00
-- url     : https://prove2.me/submissions/7f481bef-9354-4485-a961-2b6748130a59

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
import Definitions.Def_Section5Verified_Section5OrientationAmplification
import Definitions.Def_Section5Verified_Section5OrientationDecision
import Definitions.Def_Section5Verified_Section5ThreeQEXMeasurement
import Mathlib
import Theorems.Thm_section5_qex_weighted_measurement
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

theorem section5_tensor_prob {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (ψ : EuclideanSpace ℂ ι) (φ : EuclideanSpace ℂ κ) (x : ι) (y : κ) :
    prob (tensorVec ψ φ) (x,y)=prob ψ x*prob φ y := by
  simp [prob,ket,EuclideanSpace.inner_single_left,tensorVec,mul_pow]











end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership
theorem solution {n q : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (G : Qubits (n*q+1) × Qubits (n*q+1) × Qubits (n*q+1) → ℝ) :
    (∑ z, prob (section5_three_qex_state (q:=q) w) z*G z)=
      ∑ x, section5_three_qex_weight n q x*G (section5_labelled_three_qex_outcome w x) := by
  simp only [section5_three_qex_state,section5_tensor_prob,Fintype.sum_prod_type]
  calc
    _ = ∑ z1 : Qubits (n*q+1), prob (qexKet (q:=q) w) z1*
        (∑ z2 : Qubits (n*q+1), prob (qexKet (q:=q) w) z2*
          (∑ z3 : Qubits (n*q+1), prob (qexKet (q:=q) w) z3*G (z1,z2,z3))) := by
      simp only [Finset.mul_sum,mul_assoc]
    _ = ∑ x1 : Qubits (n*q), section5_qex_distribution n q x1*
        (∑ x2 : Qubits (n*q), section5_qex_distribution n q x2*
          (∑ x3 : Qubits (n*q), section5_qex_distribution n q x3*
            G (section5_labelled_qex_outcome w x1,section5_labelled_qex_outcome w x2,
              section5_labelled_qex_outcome w x3))) := by
      simp_rw [section5_qex_weighted_measurement]
      rfl
    _ = _ := by
      simp only [section5_three_qex_weight,section5_labelled_three_qex_outcome,
        Finset.mul_sum,mul_assoc]
