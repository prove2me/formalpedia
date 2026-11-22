-- Prove2me | Theorems.Thm_Autoconvolutions_Estimate_height_mono
-- name    : Autoconvolutions.Estimate.height_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:48:52.929295+00:00
-- url     : https://prove2.me/theorems/c221f787-be5b-4dea-aa1c-b0c04d5f0997
-- title:
--   Estimate: height mono
-- statement:
--   Monotonicity up to `2n`, so that levels in the construction are controlled
--   above by `A_{2K}` and below by `A_0`.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Estimate.lean#L41-L59
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Estimate.lean#L41-L59

module
public import Definitions.Def_Autoconvolutions_Definitions
public import Definitions.Def_Autoconvolutions_Parameters
public import Definitions.Def_Autoconvolutions_Digits
public import Definitions.Def_Autoconvolutions_Levels
public import Definitions.Def_Autoconvolutions_Estimate
set_option autoImplicit true
@[expose] public section
public section
open Finset
open Autoconvolutions Autoconvolutions.Estimate

theorem Autoconvolutions.Estimate.height_mono {n i j : ℕ} (hij : i ≤ j) (hj : j ≤ 2*n) :
    height n i ≤ height n j := by sorry
