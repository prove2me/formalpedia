-- Prove2me | solution 1 for section5_qex_weighted_measurement
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:56:52.546867+00:00
-- url     : https://prove2.me/submissions/2bfc5fe9-9c62-41aa-a02f-ea2454a62506

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
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

/-! Three finite-QEX votes amplify orientation success, for either sign. -/



theorem section5_qex_distribution_nonneg (n q : ℕ) (z : Qubits (n*q)) :
    0 ≤ section5_qex_distribution n q z := by
  exact div_nonneg (Real.exp_pos _).le (Finset.sum_nonneg (fun x _ => (Real.exp_pos _).le))









end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

/-! Exact Born probabilities of the published finite QEX state. The label bit
is deterministic given the spatial outcome, with the source's negative-label
convention; the spatial marginal is exactly the finite Gaussian distribution. -/

theorem section5_qex_probability_snoc {n q : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (x : Qubits (n*q)) (b : Bool) :
    prob (qexKet (q:=q) w) (Fin.snoc x b)=
      if b=decide (ltf w 0 (gridPoint x)= -1) then section5_qex_distribution n q x else 0 := by
  classical
  simp only [prob,ket,EuclideanSpace.inner_single_left,map_one,one_mul,qexKet,
    Fin.snoc_castSucc,Fin.snoc_last]
  split_ifs with h
  · change ‖(Real.sqrt (section5_qex_distribution n q x):ℂ)‖^2=section5_qex_distribution n q x
    simpa only [Complex.norm_real,Real.norm_eq_abs,sq_abs] using
      Real.sq_sqrt (section5_qex_distribution_nonneg n q x)
  · simp







end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership
theorem solution {n q : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (G : Qubits (n*q+1) → ℝ) :
    (∑ z : Qubits (n*q+1), prob (qexKet (q:=q) w) z*G z)=
      ∑ x : Qubits (n*q), section5_qex_distribution n q x*
        G (Fin.snoc x (decide (ltf w 0 (gridPoint x)= -1))) := by
  classical
  have hsnoc (b : Bool) (x : Qubits (n*q)) :
      (Fin.snocEquiv (fun _ : Fin (n*q+1) => Bool)) (b,x)=Fin.snoc x b := rfl
  rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (n*q+1) => Bool))]
  simp only [Fintype.sum_prod_type,hsnoc,section5_qex_probability_snoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  cases h : decide (ltf w 0 (gridPoint x)= -1) <;> simp [h]
