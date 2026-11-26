-- Prove2me | Theorems.Thm_Auto_aux_derivmul_aemeasurable_local
-- name    : Auto.aux_derivmul_aemeasurable_local
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:39:47.265085+00:00
-- url     : https://prove2.me/theorems/2a84ef01-7f31-54a6-952a-19b53d48c852
-- title:
--   Auto: aux derivmul aemeasurable local
-- statement:
--   Measurability of the weighted derivative on an interval.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L679-L696
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L679-L696

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_derivmul_aemeasurable_local {α β x y : ℝ} (hαβ : α < β)
    (hx : x ∈ Set.Icc α β) (hy : y ∈ Set.Icc α β) (a : ℝ → ℝ)
    (ha : ContDiffOn ℝ 1 a (Set.Icc α β)) :
    AEMeasurable (fun t ↦ ‖t * deriv a t‖ₑ)
      ((aux_logarithmicMeasure α β).restrict (Set.Icc x y)) := by sorry
