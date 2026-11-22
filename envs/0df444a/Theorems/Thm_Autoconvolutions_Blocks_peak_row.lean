-- Prove2me | Theorems.Thm_Autoconvolutions_Blocks_peak_row
-- name    : Autoconvolutions.Blocks.peak_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:47.934356+00:00
-- url     : https://prove2.me/theorems/1fa276fa-e0c1-4c44-a792-e82bac6aa066
-- title:
--   Blocks: peak row
-- statement:
--   The Blocks construction uses the peak row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/GoodBlocks.lean#L37-L41
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/GoodBlocks.lean#L37-L41

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

theorem Autoconvolutions.Blocks.peak_row {m n K D h : ℕ} {I J : Finset (Fin m)} {x : Peak m}
    (hx : x ∈ peakSet I J n K) (hh : h < D) :
    (x.2,h) ∈ rows I J (2*n-x.1) (2*n+x.1) D := by sorry
