-- Prove2me | solution 1 for section5_three_quantized_orientation_error
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:54:32.832081+00:00
-- url     : https://prove2.me/submissions/ed5bb2f0-ec01-450d-8556-3e12fb181c5b

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
import Definitions.Def_Section5Verified_Section5QuantizedOrientation
import Mathlib
import Theorems.Thm_section5_quantized_orientation_quarter
import Theorems.Thm_section5_three_independent_errors
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
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership
theorem solution (n q : ℕ) (hn : 1 ≤ n)
    (hgrid : (2:ℝ)^40*(n:ℝ)^2 ≤ (2:ℝ)^q)
    (w u : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) (hu : ‖u‖=1)
    (flip : Bool) (hclose : ‖(if flip then -u else u)-w‖ ≤ 1/6) :
    open Classical in
    (∑ a : Qubits (n*q), ∑ b : Qubits (n*q), ∑ c : Qubits (n*q),
      if (section5_quantized_orientation_error w u flip a ∧ section5_quantized_orientation_error w u flip b) ∨
        (section5_quantized_orientation_error w u flip a ∧ section5_quantized_orientation_error w u flip c) ∨
        (section5_quantized_orientation_error w u flip b ∧ section5_quantized_orientation_error w u flip c)
      then section5_qex_distribution n q a*section5_qex_distribution n q b*
        section5_qex_distribution n q c else 0) ≤ 5/32 := by
  classical
  let p := section5_qex_distribution n q
  let P : Qubits (n*q) → Prop := section5_quantized_orientation_error w u flip
  have hp : ∀ z, 0 ≤ p z := section5_qex_distribution_nonneg n q
  have hsum : ∑ z, p z=1 := section5_qex_distribution_sum n q
  have hbad : ∑ z ∈ Finset.univ.filter P, p z ≤ 1/4 := by
    rw [Finset.sum_filter]
    exact section5_quantized_orientation_quarter n q hn hgrid w u hw hu flip hclose
  exact section5_three_independent_errors p p p hp hp hp hsum hsum hsum P P P hbad hbad hbad
