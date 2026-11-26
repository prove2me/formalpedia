-- Prove2me | Theorems.Thm_Erdos266_radius_le
-- name    : Erdos266.radius_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:02:07.865168+00:00
-- url     : https://prove2.me/theorems/8047927c-b340-5223-8615-2573d14b708d
-- title:
--   Erdos266: radius le
-- statement:
--   The invariant radius is dominated by `1/N k`.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L351-L373
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L351-L373

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.radius_le {k i : ℕ} (_hk : 2 ≤ k) :
    εA (dOf k) * bigM k / (bigN k : ℝ) ^ (i + 2) ≤ ((bigN k : ℝ))⁻¹ := by sorry
