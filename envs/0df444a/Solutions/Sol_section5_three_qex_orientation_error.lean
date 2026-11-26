-- Prove2me | solution 1 for section5_three_qex_orientation_error
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:42:03.21404+00:00
-- url     : https://prove2.me/submissions/516693c4-9a00-46ad-8e0d-95aa824f5603

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5OrientationAmplification
import Mathlib
import Theorems.Thm_section5_qex_negative_orientation_vote_quarter
import Theorems.Thm_section5_qex_orientation_vote_quarter
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



theorem section5_orientation_error_quarter (n q : ℕ) (hn : 1 ≤ n) (ε : ℝ)
    (hε : 0 < ε) (hε' : ε < 1)
    (hgrid : 1073741824*(n:ℝ)^2/ε^2 ≤ (2:ℝ)^q)
    (w u : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) (hu : ‖u‖=1)
    (flip : Bool) (hclose : ‖(if flip then -u else u)-w‖ ≤ ε/6) :
    open Classical in
    (∑ z : Qubits (n*q), if section5_orientation_error w u flip z then
      section5_qex_distribution n q z else 0) ≤ 1/4 := by
  classical
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hbase : 1073741824*(n:ℝ)^2 ≤ (2:ℝ)^q := by
    have hsquare : ε^2 ≤ 1 := by nlinarith
    have hmul := (div_le_iff₀ (sq_pos_of_pos hε)).mp hgrid
    have hm := mul_le_mul_of_nonneg_left hsquare (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) q)
    nlinarith
  have hq : 0 < q := by
    by_contra hz
    have hq0 : q=0 := by omega
    rw [hq0,pow_zero] at hbase
    nlinarith
  cases flip with
  | false =>
    have hc : ‖w-u‖ ≤ 1/6 := by
      simp only [Bool.false_eq_true,↓reduceIte] at hclose
      rw [norm_sub_rev] at hclose
      linarith
    simpa [section5_orientation_error,section5_qex_distribution] using
      section5_qex_orientation_vote_quarter n q hn hq hbase w u hw hu hc
  | true =>
    have hc : ‖w+u‖ ≤ 1/6 := by
      simp only [↓reduceIte] at hclose
      have heq : -u-w=-(w+u) := by abel
      rw [heq,norm_neg] at hclose
      linarith
    simpa [section5_orientation_error,section5_qex_distribution] using
      section5_qex_negative_orientation_vote_quarter n q hn hq hbase w u hw hu hc



end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership
theorem solution (n q : ℕ) (hn : 1 ≤ n) (ε : ℝ)
    (hε : 0 < ε) (hε' : ε < 1)
    (hgrid : 1073741824*(n:ℝ)^2/ε^2 ≤ (2:ℝ)^q)
    (w u : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) (hu : ‖u‖=1)
    (flip : Bool) (hclose : ‖(if flip then -u else u)-w‖ ≤ ε/6) :
    open Classical in
    (∑ a : Qubits (n*q), ∑ b : Qubits (n*q), ∑ c : Qubits (n*q),
      if (section5_orientation_error w u flip a ∧ section5_orientation_error w u flip b) ∨
        (section5_orientation_error w u flip a ∧ section5_orientation_error w u flip c) ∨
        (section5_orientation_error w u flip b ∧ section5_orientation_error w u flip c)
      then section5_qex_distribution n q a*section5_qex_distribution n q b*
        section5_qex_distribution n q c else 0) ≤ 5/32 := by
  classical
  let p := section5_qex_distribution n q
  let P : Qubits (n*q) → Prop := section5_orientation_error w u flip
  have hp : ∀ z, 0 ≤ p z := section5_qex_distribution_nonneg n q
  have hsum : ∑ z, p z=1 := section5_qex_distribution_sum n q
  have hbad : ∑ z ∈ Finset.univ.filter P, p z ≤ 1/4 := by
    rw [Finset.sum_filter]
    exact section5_orientation_error_quarter n q hn ε hε hε' hgrid w u hw hu flip hclose
  exact section5_three_independent_errors p p p hp hp hp hsum hsum hsum P P P hbad hbad hbad
