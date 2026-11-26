-- Prove2me | Theorems.Thm_Auto_SchwartzMap_memW0
-- name    : Auto.SchwartzMap.memW0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:53:14.288844+00:00
-- url     : https://prove2.me/theorems/ef518036-bde5-5c03-8072-6257070179e3
-- title:
--   Schwartz Map: mem W0
-- statement:
--   **Proposition.**
--
--   We have $\mathcal{S}(\mathbb{R}^n)\subset W_0(\mathbb{R}^n)$.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2030-L2086
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2030-L2086

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.SchwartzMap.memW0 {d : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜] [NormedSpace ℝ 𝕜]
    (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) 𝕜) :
    MemW0 f := by sorry
