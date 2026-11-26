-- Prove2me | Theorems.Thm_Auto_aux_chain_first_ftc
-- name    : Auto.aux_chain_first_ftc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:40:12.775236+00:00
-- url     : https://prove2.me/theorems/2f9df2f5-d365-4707-94db-afff9585d1b3
-- title:
--   Auto: aux chain first ftc
-- statement:
--   The first finite-variation FTC estimate for one fixed monotone chain.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L802-L837
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L802-L837

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_chain_first_ftc {J : ℕ} {α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    (a : ℝ → ℝ) (ha : ContDiffOn ℝ 1 a (Set.Icc α β))
    (t : Fin (J + 1) → Set.Icc α β) (ht : Monotone t) :
    (∑ j : Fin J,
      (‖a (t j.succ) - a (t j.castSucc)‖₊ : ℝ≥0∞) ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) ≤
      (ENNReal.ofReal ((β - α) / α)) ^ ((2 : ℝ)⁻¹) *
        aux_logarithmicL2 α β (fun t ↦ t * deriv a t) := by sorry
