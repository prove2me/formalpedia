-- Prove2me | Theorems.Thm_Auto_aux_rpow_interpolation_constant
-- name    : Auto.aux_rpow_interpolation_constant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:48:18.71239+00:00
-- url     : https://prove2.me/theorems/9d884187-63a0-4902-a45e-d0d91260d6df
-- title:
--   Auto: aux rpow interpolation constant
-- statement:
--   Algebraic normalization of the interpolation constant to the form in the source draft.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1258-L1280
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1258-L1280

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_rpow_interpolation_constant {I V q : ℝ} (hI : 0 ≤ I) (hV : 0 < V)
    (hq : 1 ≤ q) :
    I ^ q⁻¹ * (I / V) ^ (1 - q⁻¹) = V ^ (q⁻¹ - 1) * I := by sorry
