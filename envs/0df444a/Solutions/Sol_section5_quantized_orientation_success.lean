-- Prove2me | solution 1 for section5_quantized_orientation_success
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:59:41.072074+00:00
-- url     : https://prove2.me/submissions/ced5bf76-d868-407d-9658-ddc7e77ecfc4

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
import Definitions.Def_Section5Verified_Section5OrientationAmplification
import Definitions.Def_Section5Verified_Section5OrientationDecision
import Definitions.Def_Section5Verified_Section5QuantizedOrientation
import Mathlib
import Theorems.Thm_section5_majority_decision_correct
import Theorems.Thm_section5_three_quantized_orientation_error
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

/-! Three finite-QEX votes amplify orientation success, for either sign. -/



theorem section5_qex_distribution_nonneg (n q : ℕ) (z : Qubits (n*q)) :
    0 ≤ section5_qex_distribution n q z := by
  exact div_nonneg (Real.exp_pos _).le (Finset.sum_nonneg (fun x _ => (Real.exp_pos _).le))

theorem section5_qex_distribution_sum (n q : ℕ) : ∑ z, section5_qex_distribution n q z=1 := by
  have hZ : 0 < ∑ x : Qubits (n*q), gridWeight x :=
    Finset.sum_pos (fun x _ => Real.exp_pos _) Finset.univ_nonempty
  unfold section5_qex_distribution
  rw [← Finset.sum_div,div_self hZ.ne']







end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

/-! The actual majority decision outputs a direction close to w, rather than merely
bounding an abstract error predicate. -/













theorem section5_three_qex_weight_nonneg (n q : ℕ)
    (z : Qubits (n*q) × Qubits (n*q) × Qubits (n*q)) : 0 ≤ section5_three_qex_weight n q z := by
  exact mul_nonneg (mul_nonneg (section5_qex_distribution_nonneg n q z.1)
    (section5_qex_distribution_nonneg n q z.2.1)) (section5_qex_distribution_nonneg n q z.2.2)

theorem section5_three_qex_weight_sum (n q : ℕ) : ∑ z,section5_three_qex_weight n q z=1 := by
  simp only [section5_three_qex_weight,Fintype.sum_prod_type,← Finset.mul_sum,
    section5_qex_distribution_sum,mul_one]





end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership
open Classical in
theorem solution (n q : ℕ) (hn : 1 ≤ n)
    (hgrid : (2:ℝ)^40*(n:ℝ)^2 ≤ (2:ℝ)^q)
    (w u : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) (hu : ‖u‖=1)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    (flip : Bool) (hclose : ‖(if flip then -u else u)-w‖ ≤ ε/6) :
    (∑ z : Qubits (n*q) × Qubits (n*q) × Qubits (n*q),
      if ‖section5_oriented_direction w u z-w‖ ≤ ε then section5_three_qex_weight n q z else 0) ≥ 27/32 := by
  classical
  let P := section5_quantized_majority_error (q:=q) w u flip
  let A := fun z => ‖section5_oriented_direction (q:=q) w u z-w‖ ≤ ε
  let p := section5_three_qex_weight n q
  have hbad : (∑ z, if P z then p z else 0) ≤ 5/32 := by
    simpa only [P,p,section5_quantized_majority_error,section5_three_qex_weight,
      Fintype.sum_prod_type] using
      section5_three_quantized_orientation_error n q hn hgrid w u hw hu flip (by linarith)
  have hcover : 1 ≤ (∑ z, if A z then p z else 0)+(∑ z, if P z then p z else 0) := by
    rw [← section5_three_qex_weight_sum n q,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro z hz
    have hp : 0 ≤ p z := section5_three_qex_weight_nonneg n q z
    by_cases hP : P z
    · simp only [hP,↓reduceIte]
      split_ifs <;> linarith
    · have hA : A z := by
        change ‖section5_oriented_direction w u z-w‖ ≤ ε
        rw [section5_majority_decision_correct w u flip z hP]
        linarith
      simp only [hA,hP,↓reduceIte,add_zero]
      rfl
  change (∑ z,if A z then p z else 0) ≥ _
  linarith
