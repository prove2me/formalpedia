-- Prove2me | Theorems.Thm_Auto_aux_pairwise_square_le_lintegral
-- name    : Auto.aux_pairwise_square_le_lintegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:40:14.052534+00:00
-- url     : https://prove2.me/theorems/0f3bb82c-64ce-4d70-9c21-4e6746047a27
-- title:
--   Auto: aux pairwise square le lintegral
-- statement:
--   Pairwise squared variation is controlled by the unweighted product
--   integral.  The crossing case is split at an intermediate zero.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L913-L980
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L913-L980

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_pairwise_square_le_lintegral {α β x y : ℝ} (a : ℝ → ℝ)
    (ha : ContDiffOn ℝ 1 a (Set.Icc α β))
    (hx : x ∈ Set.Icc α β) (hy : y ∈ Set.Icc α β) (hxy : x ≤ y) :
    ‖a y - a x‖ₑ ^ (2 : ℕ) ≤
      8 * ∫⁻ z in Set.Ioc x y, ‖a z‖ₑ * ‖deriv a z‖ₑ := by sorry
