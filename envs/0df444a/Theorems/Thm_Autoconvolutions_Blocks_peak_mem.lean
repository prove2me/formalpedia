-- Prove2me | Theorems.Thm_Autoconvolutions_Blocks_peak_mem
-- name    : Autoconvolutions.Blocks.peak_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:08.296798+00:00
-- url     : https://prove2.me/theorems/cd88cf61-b618-467b-8713-d4905699e9cf
-- title:
--   Blocks: peak mem
-- statement:
--   The Blocks construction uses the peak mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/GoodBlocks.lean#L32-L35
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/GoodBlocks.lean#L32-L35

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

theorem Autoconvolutions.Blocks.peak_mem {m n K : ℕ} {I J : Finset (Fin m)} {x : Peak m} (hx : x ∈ peakSet I J n K) :
    x.1 ≤ K ∧ x.2.1 ∈ goodVectors I (2*n-x.1) ∧ x.2.2 ∈ goodVectors J (2*n+x.1) := by sorry
