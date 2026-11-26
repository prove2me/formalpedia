-- Prove2me | Theorems.Thm_Erdos266_inv_inf
-- name    : Erdos266.inv_inf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:01:12.766298+00:00
-- url     : https://prove2.me/theorems/6fa16e40-282c-4463-9f88-7f39c2751569
-- title:
--   Erdos266: inv inf
-- statement:
--   The invariant, for the limit objects.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L115-L125
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L115-L125

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.inv_inf {k : ℕ} (hk : 2 ≤ k) {i : ℕ} (hi : i < dOf k) :
    |finSum i k Sinf + tailAnchor (i + 1) k - (xinf i : ℝ)|
      ≤ εA (dOf k) * bigM k / (bigN k : ℝ) ^ (i + 2) := by sorry
