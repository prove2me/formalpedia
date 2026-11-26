-- Prove2me | solution 1 for section5_tomography_orientation_joint_success
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T21:04:19.483836+00:00
-- url     : https://prove2.me/submissions/d5afd51c-37e9-403b-9047-e74e471aa34e

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
import Mathlib
import Theorems.Thm_section5_quantized_orientation_success
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

/-! The actual majority decision outputs a direction close to w, rather than merely
bounding an abstract error predicate. -/













theorem section5_three_qex_weight_nonneg (n q : ℕ)
    (z : Qubits (n*q) × Qubits (n*q) × Qubits (n*q)) : 0 ≤ section5_three_qex_weight n q z := by
  exact mul_nonneg (mul_nonneg (section5_qex_distribution_nonneg n q z.1)
    (section5_qex_distribution_nonneg n q z.2.1)) (section5_qex_distribution_nonneg n q z.2.2)







end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership
open Classical in
theorem solution {T : Type*} [Fintype T]
    (n q : ℕ) (hn : 1 ≤ n) (hgrid : (2:ℝ)^40*(n:ℝ)^2 ≤ (2:ℝ)^q)
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1)
    (u : T → EuclideanSpace ℝ (Fin n)) (hu : ∀ t, ‖u t‖=1)
    (p : T → ℝ) (hp : ∀ t, 0 ≤ p t) (hpsum : ∑ t,p t=1)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    (hgood : (∑ t : T, if ∃ flip : Bool, ‖(if flip then -(u t) else u t)-w‖ ≤ ε/6 then p t else 0) ≥ 11/12) :
    (∑ t : T, ∑ z : Qubits (n*q) × Qubits (n*q) × Qubits (n*q),
      if ‖section5_oriented_direction w (u t) z-w‖ ≤ ε then
        p t*section5_three_qex_weight n q z else 0) ≥ 73/96 := by
  classical
  let S := fun t : T => ∑ z : Qubits (n*q) × Qubits (n*q) × Qubits (n*q),
    if ‖section5_oriented_direction w (u t) z-w‖ ≤ ε then section5_three_qex_weight n q z else 0
  let G := fun t : T => ∃ flip : Bool, ‖(if flip then -(u t) else u t)-w‖ ≤ ε/6
  have hSnonneg (t : T) : 0 ≤ S t := Finset.sum_nonneg (fun z hz => by
    split_ifs
    · exact section5_three_qex_weight_nonneg n q z
    · exact le_refl 0)
  have hform : (∑ t : T, ∑ z : Qubits (n*q) × Qubits (n*q) × Qubits (n*q),
      if ‖section5_oriented_direction w (u t) z-w‖ ≤ ε then
        p t*section5_three_qex_weight n q z else 0)=∑ t : T,p t*S t := by
    apply Finset.sum_congr rfl
    intro t ht
    dsimp only [S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    split_ifs <;> simp
  rw [hform]
  have hlower : (27/32:ℝ)*(∑ t : T,if G t then p t else 0) ≤ ∑ t : T,p t*S t := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    by_cases hg : G t
    · obtain ⟨flip,hclose⟩ := hg
      have hs : 27/32 ≤ S t := section5_quantized_orientation_success n q hn hgrid
        w (u t) hw (hu t) ε hε hε' flip hclose
      have hG : G t := ⟨flip,hclose⟩
      simp only [hG,↓reduceIte]
      nlinarith [mul_le_mul_of_nonneg_left hs (hp t)]
    · simp only [hg,↓reduceIte,mul_zero]
      exact mul_nonneg (hp t) (hSnonneg t)
  change (∑ t : T,if G t then p t else 0) ≥ _ at hgood
  nlinarith
