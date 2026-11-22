-- Prove2me | Theorems.Thm_Autoconvolutions_Blocks_peak_sum
-- name    : Autoconvolutions.Blocks.peak_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:55.751602+00:00
-- url     : https://prove2.me/theorems/6726192c-0096-4030-b120-8ea340befb9c
-- title:
--   Blocks: peak sum
-- statement:
--   Summing `s A_s²` once per plateau gives exactly the binomial sum in §2.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/GoodBlocks.lean#L66-L73
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/GoodBlocks.lean#L66-L73

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

theorem Autoconvolutions.Blocks.peak_sum {m : ℕ} (I J : Finset (Fin m)) (n K : ℕ) :
    (∑ x ∈ peakSet I J n K, (x.1:ℝ) * (Estimate.height n x.1)^2) =
      ∑ s ∈ range (K+1), (s:ℝ)*Estimate.count n I.card J.card s*(Estimate.height n s)^2 := by sorry
