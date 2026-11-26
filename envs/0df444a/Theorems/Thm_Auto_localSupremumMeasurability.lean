-- Prove2me | Theorems.Thm_Auto_localSupremumMeasurability
-- name    : Auto.localSupremumMeasurability
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:49:54.465781+00:00
-- url     : https://prove2.me/theorems/6c6b2d96-706a-5250-beae-72e9f1fa5777
-- title:
--   Auto: local Supremum Measurability
-- statement:
--   **Proposition.**
--
--   Let $d\in \mathbb{N}$ and $f:\mathbb{R}^d\to \mathbb{K}$ be continuous.
--   Then for $r\in (0,\infty)$, the function $g:\mathbb{R}^d\to [0,\infty]$  defined by
--
--   $$
--       g(x)=\sup_{|x-y|\le r}|f(y)|
--   $$
--
--   is finite and upper semi continuous and measurable.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L125-L128
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L125-L128

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.localSupremumMeasurability {d : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : Continuous f) {r : ℝ} (_hr : 0 < r) :
    UpperSemicontinuous (wienerEnvelope f r) ∧ Measurable (wienerEnvelope f r) := by sorry
