-- Prove2me | Theorems.Thm_Auto_aux_ErgodicBox_eLpNorm_count_sq_eq_finset_sum_rpow
-- name    : Auto.aux_ErgodicBox.eLpNorm_count_sq_eq_finset_sum_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:44:12.576088+00:00
-- url     : https://prove2.me/theorems/12cf37a4-8c0c-4c51-bf27-d9e8c933d67c
-- title:
--   aux Ergodic Box: e Lp Norm count sq eq finset sum rpow
-- statement:
--   The aux Ergodic Box construction uses the e Lp Norm count sq eq finset sum rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2532-L2548
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2532-L2548

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

theorem Auto.aux_ErgodicBox.eLpNorm_count_sq_eq_finset_sum_rpow
    {κ : Type*} [MeasurableSpace κ] [Countable κ] [MeasurableSingletonClass κ]
    (B : Finset κ) (F : κ → ℝ) (p : ℝ≥0∞)
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) (hpreal : 0 < p.toReal)
    (hF : ∀ k, k ∉ B → F k = 0) :
    eLpNorm F p Measure.count ^ 2 =
      (∑ k ∈ B, ‖F k‖ₑ ^ p.toReal) ^ (2 / p.toReal) := by sorry
