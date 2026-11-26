-- Prove2me | Theorems.Thm_Auto_aux_eLpNorm_top_le_of_bound
-- name    : Auto.aux_eLpNorm_top_le_of_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:48:09.472854+00:00
-- url     : https://prove2.me/theorems/762b03cc-b647-4bac-a680-e5697925b2d6
-- title:
--   Auto: aux e Lp Norm top le of bound
-- statement:
--   A pointwise norm bound is an extended `L∞` estimate.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1140-L1145
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1140-L1145

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_eLpNorm_top_le_of_bound
    {E 𝕜 : Type*} [MeasurableSpace E] [NormedAddCommGroup 𝕜] {μ : Measure E}
    {f : E → 𝕜} {B : ℝ} (hB : ∀ᵐ x ∂μ, ‖f x‖ ≤ B) :
    eLpNorm f ∞ μ ≤ ENNReal.ofReal B := by sorry
