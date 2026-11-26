-- Prove2me | Theorems.Thm_Auto_ct_calderon_transference_external
-- name    : Auto.ct_calderon_transference_external
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:54:23.621802+00:00
-- url     : https://prove2.me/theorems/0647c143-35de-5fe7-b525-8cce7c6e9fab
-- title:
--   Auto: ct calderon transference external
-- statement:
--   Calderón transference for the multilinear averages defined in this
--   Mathlib-only module.  The explicit transference factor is
--   `calderonTransferenceConstant n = 2 ^ (4 * n + 6)`; thus an input constant
--   `C` is transferred with constant `C * calderonTransferenceConstant n`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L3108-L3130
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L3108-L3130

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

theorem Auto.ct_calderon_transference_external {n : ℕ} (hn : 2 ≤ n)
    (p : Fin n → ℝ≥0∞) (hp : ∀ i, 1 < p i ∧ p i < ∞)
    (hsum : (∑ i, ((p i)⁻¹).toReal) = 1 / 2) (C : ℝ) (_hC : 0 < C) :
    0 < calderonTransferenceConstant n ∧ ∀ g : ℕ → ℝ,
      (∀ J, 0 < J → 1 ≤ g J) →
      realVariableJumpBound p C g →
        realErgodicJumpBound.{u} p (calderonTransferenceConstant n * C) g := by sorry
