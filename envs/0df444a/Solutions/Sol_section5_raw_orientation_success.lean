-- Prove2me | solution 1 for section5_raw_orientation_success
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T21:03:54.832084+00:00
-- url     : https://prove2.me/submissions/486a024b-8182-42ff-a019-b0d6361b6a38

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
import Theorems.Thm_section5_quantized_orientation_success
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership QuantumLTF.Example

/-! The classical output may be an unnormalized fixed-point vector. Its labels
coincide with those of its normalization, including the zero-margin convention. -/

theorem section5_ltf_positive_smul {n : ℕ} (c : ℝ) (hc : 0 < c)
    (r x : EuclideanSpace ℝ (Fin n)) : ltf (c • r) 0 x=ltf r 0 x := by
  simp only [ltf,inner_smul_left,conj_trivial,sub_zero,sgn]
  simp only [mul_nonneg_iff_of_pos_left hc]

theorem section5_ltf_normalize {n : ℕ} (r x : EuclideanSpace ℝ (Fin n)) (hr : r ≠ 0) :
    ltf (NormedSpace.normalize r) 0 x=ltf r 0 x :=
  section5_ltf_positive_smul _ (inv_pos.mpr (norm_pos_iff.mpr hr)) r x

theorem section5_quantized_vote_normalize {n q : ℕ} (w r : EuclideanSpace ℝ (Fin n))
    (hr : r ≠ 0) (z : Qubits (n*q)) :
    section5_quantized_vote w (NormedSpace.normalize r) z=section5_quantized_vote w r z := by
  unfold section5_quantized_vote
  rw [section5_ltf_normalize r _ hr]

theorem section5_oriented_normalize {n q : ℕ} (w r : EuclideanSpace ℝ (Fin n))
    (hr : r ≠ 0) (z : Qubits (n*q) × Qubits (n*q) × Qubits (n*q)) :
    NormedSpace.normalize (section5_oriented_direction w r z)=
      section5_oriented_direction w (NormedSpace.normalize r) z := by
  simp only [section5_oriented_direction,section5_quantized_vote_normalize w r hr]
  split_ifs <;> simp [NormedSpace.normalize_neg]

theorem section5_oriented_ne_zero {n q : ℕ} (w r : EuclideanSpace ℝ (Fin n))
    (hr : r ≠ 0) (z : Qubits (n*q) × Qubits (n*q) × Qubits (n*q)) :
    section5_oriented_direction w r z ≠ 0 := by
  unfold section5_oriented_direction
  split_ifs
  · exact neg_ne_zero.mpr hr
  · exact hr







end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Example
open Classical in
theorem solution (n q : ℕ) (hn : 1 ≤ n)
    (hgrid : (2:ℝ)^40*(n:ℝ)^2 ≤ (2:ℝ)^q)
    (w r : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) (hr : r ≠ 0)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    (flip : Bool) (hclose : ‖(if flip then -NormedSpace.normalize r else NormedSpace.normalize r)-w‖ ≤ ε/6) :
    (∑ z : Qubits (n*q) × Qubits (n*q) × Qubits (n*q),
      if section5_oriented_direction w r z ≠ 0 ∧
          ‖NormedSpace.normalize (section5_oriented_direction w r z)-w‖ ≤ ε then
        section5_three_qex_weight n q z else 0) ≥ 27/32 := by
  have hh := section5_quantized_orientation_success n q hn hgrid w (NormedSpace.normalize r)
    hw (NormedSpace.norm_normalize hr) ε hε hε' flip hclose
  convert hh using 1
  apply Finset.sum_congr rfl
  intro z hz
  have hne : section5_oriented_direction (q:=q) w r z ≠ 0 := section5_oriented_ne_zero w r hr z
  have hnorm := section5_oriented_normalize w r hr z
  by_cases hgood : ‖section5_oriented_direction w (NormedSpace.normalize r) z-w‖ ≤ ε
  · rw [if_pos ⟨hne,by rw [hnorm]; exact hgood⟩,if_pos hgood]
  · rw [if_neg (by intro h; apply hgood; rw [← hnorm]; exact h.2),if_neg hgood]
