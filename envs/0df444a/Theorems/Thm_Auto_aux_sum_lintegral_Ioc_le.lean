-- Prove2me | Theorems.Thm_Auto_aux_sum_lintegral_Ioc_le
-- name    : Auto.aux_sum_lintegral_Ioc_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:38:25.069789+00:00
-- url     : https://prove2.me/theorems/8d46f0c7-e006-57a0-a208-83fdd04bd3e7
-- title:
--   Auto: aux sum lintegral Ioc le
-- statement:
--   Consecutive intervals cut out by a monotone finite chain are disjoint, so
--   their nonnegative integrals are bounded by the integral on the ambient
--   interval.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L587-L613
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L587-L613

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_sum_lintegral_Ioc_le {J : ℕ} {μ : Measure ℝ}
    (t : Fin (J + 1) → ℝ) (ht : Monotone t) (f : ℝ → ℝ≥0∞)
    {α β : ℝ} (hα : α ≤ t 0) (hβ : t (Fin.last J) ≤ β) :
    (∑ j : Fin J, ∫⁻ x in Set.Ioc (t j.castSucc) (t j.succ), f x ∂μ) ≤
      ∫⁻ x in Set.Icc α β, f x ∂μ := by sorry
