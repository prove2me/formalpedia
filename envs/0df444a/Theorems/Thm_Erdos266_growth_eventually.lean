-- Prove2me | Theorems.Thm_Erdos266_growth_eventually
-- name    : Erdos266.growth_eventually
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:42:48.200691+00:00
-- url     : https://prove2.me/theorems/22ea0bc5-a828-430e-a095-9527751a4f54
-- title:
--   Erdos266: growth eventually
-- statement:
--   **The eventual-domination condition** that admits dimension `d` into the
--   construction: for large `k` the lattice-step error at scale `k` fits inside
--   the invariant radius at scale `k+1`, uniformly in the coordinate `i < d`.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Growth.lean#L134-L248
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Growth.lean#L134-L248

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Growth
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.growth_eventually (d : ℕ) (Dc εc : ℝ) (hD : 0 < Dc) (hε : 0 < εc) :
    ∃ K₀ : ℕ, 2 ≤ K₀ ∧ ∀ k, K₀ ≤ k → ∀ i : ℕ, i < d →
      Dc * (1 / (bigN k : ℝ) ^ (i + 2) + (bigM k : ℝ) ^ 2 / (bigN k : ℝ) ^ (i + 3))
        ≤ εc * (bigM (k + 1) : ℝ) / (bigN (k + 1) : ℝ) ^ (i + 2) := by sorry
