-- Prove2me | Theorems.Thm_Auto_aux_ErgodicBox_lintegral_finite_orbit_sum
-- name    : Auto.aux_ErgodicBox.lintegral_finite_orbit_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:44:41.993169+00:00
-- url     : https://prove2.me/theorems/bb21001c-2418-45ce-b166-95faf4f2abc2
-- title:
--   aux Ergodic Box: lintegral finite orbit sum
-- statement:
--   The aux Ergodic Box construction uses the lintegral finite orbit sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2674-L2719
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2674-L2719

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

theorem Auto.aux_ErgodicBox.lintegral_finite_orbit_sum
    {X κ : Type*} [MeasurableSpace X] (μ : Measure X)
    (B : Finset κ) (T : κ → X → X)
    (hT : ∀ k ∈ B, MeasurePreserving (T k) μ μ)
    {J : ℕ} (d : Fin J → X → ℝ)
    (hd : ∀ j, AEStronglyMeasurable (d j) μ) :
    ∫⁻ x, ∑ j : Fin J, ∑ k ∈ B, ‖d j (T k x)‖ₑ ^ (2 : ℕ) ∂μ =
      B.card * ∑ j : Fin J, ∫⁻ x, ‖d j x‖ₑ ^ (2 : ℕ) ∂μ := by sorry
