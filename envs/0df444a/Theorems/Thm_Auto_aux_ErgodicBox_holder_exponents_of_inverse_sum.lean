-- Prove2me | Theorems.Thm_Auto_aux_ErgodicBox_holder_exponents_of_inverse_sum
-- name    : Auto.aux_ErgodicBox.holder_exponents_of_inverse_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:38:51.114124+00:00
-- url     : https://prove2.me/theorems/fac979dc-c71c-544a-81fb-56a8e99f2316
-- title:
--   aux Ergodic Box: holder exponents of inverse sum
-- statement:
--   The exponent normalization used by the finite-box Hölder estimate.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2777-L2800
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2777-L2800

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
open Auto.aux_ErgodicBox
open MeasureTheory Set
open scoped ENNReal BigOperators

theorem Auto.aux_ErgodicBox.holder_exponents_of_inverse_sum {n : ℕ} (p : Fin n → ℝ≥0∞)
    (hp : ∀ i, 1 < p i ∧ p i < ∞)
    (hsum : (∑ i, ((p i)⁻¹).toReal) = 1 / 2) :
    (∀ i, p i ≠ 0) ∧ (∀ i, p i ≠ ∞) ∧
      (∀ i, 0 < (p i).toReal) ∧
      ∑ i, 2 / (p i).toReal = 1 := by sorry
