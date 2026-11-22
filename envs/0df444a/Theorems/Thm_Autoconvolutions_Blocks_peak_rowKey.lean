-- Prove2me | Theorems.Thm_Autoconvolutions_Blocks_peak_rowKey
-- name    : Autoconvolutions.Blocks.peak_rowKey
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:09.121082+00:00
-- url     : https://prove2.me/theorems/9afce866-62c4-427b-998f-07f64282e09a
-- title:
--   Blocks: peak row Key
-- statement:
--   The Blocks construction uses the peak row Key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/GoodBlocks.lean#L43-L45
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/GoodBlocks.lean#L43-L45

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

theorem Autoconvolutions.Blocks.peak_rowKey {m : ℕ} (x : Peak m) (D h : ℕ) :
    rowKey D (x.2,h) = D * peakCode D x + h := by sorry
