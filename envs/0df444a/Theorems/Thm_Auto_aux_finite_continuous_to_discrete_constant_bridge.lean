-- Prove2me | Theorems.Thm_Auto_aux_finite_continuous_to_discrete_constant_bridge
-- name    : Auto.aux_finite_continuous_to_discrete_constant_bridge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:43:30.561066+00:00
-- url     : https://prove2.me/theorems/0e834e81-87c9-5607-bfc1-279f29c56dc3
-- title:
--   Auto: aux finite continuous to discrete constant bridge
-- statement:
--   Cancel the positive-volume cuboid factor in the finite lower estimate.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2283-L2334
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2283-L2334

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

theorem Auto.aux_finite_continuous_to_discrete_constant_bridge {n : ℕ}
    (C g : ℝ) (D E : ℝ≥0∞) (L F : Fin n → ℝ≥0∞)
    (hlower :
      (ENNReal.ofReal ((1 : ℝ) / 8) ^ (2 : ℝ) *
        ENNReal.ofReal ((1 : ℝ) / 8) ^ n) * D ≤ E)
    (hupper : E ≤ ENNReal.ofReal C * ENNReal.ofReal g *
      ∏ i, L i ^ (2 : ℕ))
    (hL : ∀ i, L i ≤ F i) :
    D ≤ ENNReal.ofReal (((2 : ℝ) ^ (3 * n + 6)) * C) *
      ENNReal.ofReal g * ∏ i, F i ^ (2 : ℕ) := by sorry
