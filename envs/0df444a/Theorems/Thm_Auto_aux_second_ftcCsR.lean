-- Prove2me | Theorems.Thm_Auto_aux_second_ftcCsR
-- name    : Auto.aux_second_ftcCsR
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:40:30.823823+00:00
-- url     : https://prove2.me/theorems/b14fb5ce-f327-519b-ab57-f10ee277340f
-- title:
--   Auto: aux second ftc Cs R
-- statement:
--   The `rpow`/supremum closure of the second FTC estimate.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L1100-L1130
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L1100-L1130

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_second_ftcCsR {J : ℕ} {α β : ℝ} (hα : 0 < α)
    (a : ℝ → ℝ) (ha : ContDiffOn ℝ 1 a (Set.Icc α β)) :
    (finiteVariationSeminorm (fun t : Set.Icc α β ↦ a t) 2 J) ^ (2 : ℝ) ≤
      8 * aux_logarithmicL2 α β a *
        aux_logarithmicL2 α β (fun t ↦ t * deriv a t) := by sorry
