-- Prove2me | Theorems.Thm_Erdos266_elemZ_cross
-- name    : Erdos266.elemZ_cross
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:01:38.145402+00:00
-- url     : https://prove2.me/theorems/393f7e47-5d50-4392-ad1a-399e4ac7f56a
-- title:
--   Erdos266: elem Z cross
-- statement:
--   Monotonicity across blocks.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L264-L286
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L264-L286

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.elemZ_cross {l l' j j' : ℕ} (hll : l < l') (hj : j < dOf l) (hj' : j' < dOf l') :
    elemZ l j < elemZ l' j' := by sorry
