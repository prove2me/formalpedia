-- Prove2me | Theorems.Thm_Auto_aux_realErgodicJumpBound_of_realVariable
-- name    : Auto.aux_realErgodicJumpBound_of_realVariable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:45:15.294959+00:00
-- url     : https://prove2.me/theorems/1ba51ba3-d5c3-4b54-bdeb-fce3ccd4d12d
-- title:
--   Auto: aux real Ergodic Jump Bound of real Variable
-- statement:
--   The fully internal combination of the finite cuboid reduction and the
--   finite-box orbit reduction.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L3066-L3096
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L3066-L3096

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

theorem Auto.aux_realErgodicJumpBound_of_realVariable {n : ℕ}
    (hn : 0 < n) (p : Fin n → ℝ≥0∞) (C : ℝ) (g : ℕ → ℝ)
    (hp : ∀ i, 1 < p i ∧ p i < ∞)
    (hsum : (∑ i, ((p i)⁻¹).toReal) = 1 / 2)
    (hreal : realVariableJumpBound p C g) :
    realErgodicJumpBound.{u} p
      ((2 : ℝ) ^ n * ((2 : ℝ) ^ (3 * n + 6) * C)) g := by sorry
