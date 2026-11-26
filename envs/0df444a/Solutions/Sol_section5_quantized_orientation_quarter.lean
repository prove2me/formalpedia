-- Prove2me | solution 1 for section5_quantized_orientation_quarter
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:48:47.430433+00:00
-- url     : https://prove2.me/submissions/b7c57909-5554-4c70-a79f-3734d12a27db

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
import Definitions.Def_Section5Verified_Section5BoundedWindow
import Definitions.Def_Section5Verified_Section5OrientationAmplification
import Definitions.Def_Section5Verified_Section5QuantizedOrientation
import Definitions.Def_Section5Verified_Section5RealWindow
import Mathlib
import Theorems.Thm_section5_large_grid_fits_window
import Theorems.Thm_section5_qex_negative_orientation_vote_margin
import Theorems.Thm_section5_qex_orientation_vote_margin
import Theorems.Thm_section5_uniform_qex_window_error
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

/-! Actual finite-QEX orientation probabilities after the precision-independent
coordinate truncation. The three-vote error remains at most 5/32. -/





theorem section5_finite_event_union_bound {α : Type*} [Fintype α]
    (p : α → ℝ) (hp : ∀ x, 0 ≤ p x) (P Q R : α → Prop)
    [DecidablePred P] [DecidablePred Q] [DecidablePred R]
    (hsub : ∀ x, R x → P x ∨ Q x) :
    (∑ x, if R x then p x else 0) ≤
      (∑ x, if P x then p x else 0)+(∑ x, if Q x then p x else 0) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x hx
  by_cases hr : R x
  · rcases hsub x hr with h | h <;>
      simp only [hr,h,↓reduceIte] <;> split_ifs <;> linarith [hp x]
  · simp only [hr,↓reduceIte]
    split_ifs <;> linarith [hp x]

theorem section5_orientation_error_margin (n q : ℕ) (hn : 1 ≤ n)
    (hgrid : (2:ℝ)^40*(n:ℝ)^2 ≤ (2:ℝ)^q)
    (w u : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) (hu : ‖u‖=1)
    (flip : Bool) (hclose : ‖(if flip then -u else u)-w‖ ≤ 1/6) :
    open Classical in
    (∑ z : Qubits (n*q), if section5_orientation_error w u flip z then
      section5_qex_distribution n q z else 0) ≤ 7/32 := by
  classical
  have hq : 0 < q := by have hh := section5_large_grid_fits_window n q hn hgrid; omega
  have hbase : 1073741824*(n:ℝ)^2 ≤ (2:ℝ)^q := by
    norm_num only [show (2:ℝ)^40=1099511627776 from by norm_num] at hgrid
    nlinarith [sq_nonneg (n:ℝ)]
  cases flip with
  | false =>
    have hc : ‖w-u‖ ≤ 1/6 := by
      simpa only [Bool.false_eq_true,↓reduceIte,norm_sub_rev] using hclose
    simpa [section5_orientation_error,section5_qex_distribution] using
      section5_qex_orientation_vote_margin n q hn hq hbase w u hw hu hc
  | true =>
    have hc : ‖w+u‖ ≤ 1/6 := by
      simp only [↓reduceIte] at hclose
      have heq : -u-w=-(w+u) := by abel
      rwa [heq,norm_neg] at hclose
    simpa [section5_orientation_error,section5_qex_distribution] using
      section5_qex_negative_orientation_vote_margin n q hn hq hbase w u hw hu hc





end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership
theorem solution (n q : ℕ) (hn : 1 ≤ n)
    (hgrid : (2:ℝ)^40*(n:ℝ)^2 ≤ (2:ℝ)^q)
    (w u : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) (hu : ‖u‖=1)
    (flip : Bool) (hclose : ‖(if flip then -u else u)-w‖ ≤ 1/6) :
    open Classical in
    (∑ z : Qubits (n*q), if section5_quantized_orientation_error w u flip z then
      section5_qex_distribution n q z else 0) ≤ 1/4 := by
  classical
  let P : Qubits (n*q) → Prop := section5_orientation_error w u flip
  let Q := fun z : Qubits (n*q) => ltf u 0 (gridPoint z) ≠
    ltf u 0 (section5_bounded_window_vector q (gridPoint z))
  let R : Qubits (n*q) → Prop := section5_quantized_orientation_error w u flip
  have hsub : ∀ z, R z → P z ∨ Q z := by
    intro z hz
    by_cases hq : Q z
    · exact Or.inr hq
    · have heq : ltf u 0 (gridPoint z)=ltf u 0 (section5_bounded_window_vector q (gridPoint z)) :=
        not_not.mp hq
      exact Or.inl (by simpa only [P,R,section5_orientation_error,
        section5_quantized_orientation_error,heq] using hz)
  have hh := section5_finite_event_union_bound (section5_qex_distribution n q)
    (section5_qex_distribution_nonneg n q) P Q R hsub
  have h1 := section5_orientation_error_margin n q hn hgrid w u hw hu flip hclose
  have h2 : (∑ z : Qubits (n*q), if Q z then section5_qex_distribution n q z else 0) ≤ 1/32 := by
    convert section5_uniform_qex_window_error n q hn hgrid u hu using 1
    apply Finset.sum_congr rfl
    intro z hz
    by_cases heq : ltf u 0 (gridPoint z)=ltf u 0 (section5_bounded_window_vector q (gridPoint z)) <;>
      simp [Q,section5_bounded_window_vector,section5_qex_distribution] at heq ⊢ <;>
      simp [heq]
  change (∑ z,if P z then _ else _) ≤ _ at h1
  change (∑ z,if R z then _ else _) ≤ _
  apply hh.trans
  linarith only [h1,h2]
