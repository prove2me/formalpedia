-- Prove2me | Theorems.Thm_Autoconvolutions_Blocks_peakCode_injOn
-- name    : Autoconvolutions.Blocks.peakCode_injOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:50.475184+00:00
-- url     : https://prove2.me/theorems/375e06e1-c530-42a6-9c7d-d9be6bd5c6d5
-- title:
--   Blocks: peak Code inj On
-- statement:
--   Distinct peak indices have distinct starts, even when their levels differ.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/GoodBlocks.lean#L48-L63
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/GoodBlocks.lean#L48-L63

module
public import Definitions.Def_Autoconvolutions_BlockKeys
public import Definitions.Def_Autoconvolutions_Occupancy
public import Definitions.Def_Autoconvolutions_Estimate
public import Definitions.Def_Autoconvolutions_GoodBlocks
set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped BigOperators
open Autoconvolutions Autoconvolutions.Blocks

theorem Autoconvolutions.Blocks.peakCode_injOn {m n K D : ℕ} {I J : Finset (Fin m)}
    (hD : 1 < D) (hd : Disjoint I J) (hK : K ≤ n) (hnD : 4*n < D) :
    Set.InjOn (peakCode D) (↑(peakSet I J n K) : Set (Peak m)) := by sorry
