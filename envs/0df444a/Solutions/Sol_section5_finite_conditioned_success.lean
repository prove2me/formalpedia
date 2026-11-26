-- Prove2me | solution 1 for section5_finite_conditioned_success
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:53:37.986005+00:00
-- url     : https://prove2.me/submissions/6d5cf045-2847-40aa-96db-8e6819c54606

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
import Mathlib
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Example
theorem solution {T Z : Type*} [Fintype T] [Fintype Z]
    (p : T → ℝ) (q : Z → ℝ) (hp : ∀ t, 0 ≤ p t) (hq : ∀ z, 0 ≤ q z)
    (G : T → Prop) (A : T → Z → Prop) [DecidablePred G] [∀ t, DecidablePred (A t)]
    (c g : ℝ) (hc : 0 ≤ c)
    (hgood : (∑ t,if G t then p t else 0) ≥ g)
    (hconditional : ∀ t, G t → (∑ z,if A t z then q z else 0) ≥ c) :
    (∑ t,∑ z,if A t z then p t*q z else 0) ≥ c*g := by
  let S := fun t => ∑ z,if A t z then q z else 0
  have hform : (∑ t,∑ z,if A t z then p t*q z else 0)=∑ t,p t*S t := by
    apply Finset.sum_congr rfl
    intro t ht
    dsimp only [S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    split_ifs <;> simp
  rw [hform]
  have hsum : c*(∑ t,if G t then p t else 0) ≤ ∑ t,p t*S t := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    by_cases hG : G t
    · simp only [hG,↓reduceIte]
      calc
        c*p t = p t*c := mul_comm _ _
        _ ≤ p t*S t := mul_le_mul_of_nonneg_left (hconditional t hG) (hp t)
    · simp only [hG,↓reduceIte,mul_zero]
      exact mul_nonneg (hp t) (Finset.sum_nonneg (fun z hz => by split_ifs; exact hq z; rfl))
  exact (mul_le_mul_of_nonneg_left hgood hc).trans hsum
