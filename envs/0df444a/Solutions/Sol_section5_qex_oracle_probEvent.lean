-- Prove2me | solution 1 for section5_qex_oracle_probEvent
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:59:18.939538+00:00
-- url     : https://prove2.me/submissions/66f29734-af07-486b-bd72-78441bf17361

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_probMixed
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5OrientationAmplification
import Mathlib
import Theorems.Thm_section5_qex_weighted_measurement
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

/-! Exact Born probabilities of the published finite QEX state. The label bit
is deterministic given the spatial outcome, with the source's negative-label
convention; the spatial marginal is exactly the finite Gaussian distribution. -/





theorem section5_qex_probEvent {n q : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (P : Qubits (n*q+1) → Prop) [DecidablePred P] :
    probEvent (qexKet (q:=q) w) P=
      ∑ x : Qubits (n*q), if P (Fin.snoc x (decide (ltf w 0 (gridPoint x)= -1))) then
        section5_qex_distribution n q x else 0 := by
  have hh := section5_qex_weighted_measurement w (fun z => if P z then 1 else 0)
  simpa only [probEvent,Finset.sum_filter,mul_ite,mul_one,mul_zero,ite_mul,one_mul,zero_mul]
    using hh



end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership
theorem solution {n q : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (U : Matrix (Qubits (n*q+1)) (Qubits (n*q+1)) ℂ) (hU : IsQEX (q:=q) w U)
    (P : Qubits (n*q+1) → Prop) [DecidablePred P] :
    probEvent (act U (zeroKet (n*q+1))) P=
      ∑ x : Qubits (n*q), if P (Fin.snoc x (decide (ltf w 0 (gridPoint x)= -1))) then
        section5_qex_distribution n q x else 0 := by
  have hstate : act U (zeroKet (n*q+1))=qexKet (q:=q) w :=
    congrArg (WithLp.toLp 2) hU.2
  rw [hstate]
  exact section5_qex_probEvent w P
