-- Prove2me | solution 1 for section5_raw_tomography_joint_success
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T21:10:08.74991+00:00
-- url     : https://prove2.me/submissions/7534f5a8-90c3-4c32-983f-821152b1473e

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
import Theorems.Thm_section5_finite_conditioned_success
import Theorems.Thm_section5_raw_orientation_success
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
open QAlgorithms QuantumLTF.Membership QuantumLTF.Example
open Classical in
theorem solution {T : Type*} [Fintype T]
    (n q : ℕ) (hn : 1 ≤ n) (hgrid : (2:ℝ)^40*(n:ℝ)^2 ≤ (2:ℝ)^q)
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1)
    (r : T → EuclideanSpace ℝ (Fin n)) (p : T → ℝ) (hp : ∀ t, 0 ≤ p t)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    (hgood : (∑ t,if r t ≠ 0 ∧ ∃ flip : Bool,
        ‖(if flip then -NormedSpace.normalize (r t) else NormedSpace.normalize (r t))-w‖ ≤ ε/6
      then p t else 0) ≥ 11/12) :
    (∑ t,∑ z : Qubits (n*q) × Qubits (n*q) × Qubits (n*q),
      if section5_oriented_direction w (r t) z ≠ 0 ∧
          ‖NormedSpace.normalize (section5_oriented_direction w (r t) z)-w‖ ≤ ε then
        p t*section5_three_qex_weight n q z else 0) ≥ 73/96 := by
  let G := fun t => r t ≠ 0 ∧ ∃ flip : Bool,
    ‖(if flip then -NormedSpace.normalize (r t) else NormedSpace.normalize (r t))-w‖ ≤ ε/6
  let A := fun t (z : Qubits (n*q) × Qubits (n*q) × Qubits (n*q)) =>
    section5_oriented_direction w (r t) z ≠ 0 ∧
      ‖NormedSpace.normalize (section5_oriented_direction w (r t) z)-w‖ ≤ ε
  letI : DecidablePred G := fun t => inferInstanceAs (Decidable (r t ≠ 0 ∧ ∃ flip : Bool,
    ‖(if flip then -NormedSpace.normalize (r t) else NormedSpace.normalize (r t))-w‖ ≤ ε/6))
  letI : ∀ t, DecidablePred (A t) := fun t z => inferInstanceAs (Decidable
    (section5_oriented_direction w (r t) z ≠ 0 ∧
      ‖NormedSpace.normalize (section5_oriented_direction w (r t) z)-w‖ ≤ ε))
  have hh := section5_finite_conditioned_success p (section5_three_qex_weight n q) hp
    (section5_three_qex_weight_nonneg n q) G A (27/32) (11/12) (by norm_num) hgood
    (fun t ht => by
      obtain ⟨hr,flip,hclose⟩ := ht
      exact section5_raw_orientation_success n q hn hgrid w (r t) hw hr ε hε hε' flip hclose)
  exact (show (73/96:ℝ) ≤ (27/32)*(11/12) by norm_num).trans hh
