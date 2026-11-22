-- Prove2me | Theorems.Thm_Autoconvolutions_Estimate_height_pos
-- name    : Autoconvolutions.Estimate.height_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:48:49.634576+00:00
-- url     : https://prove2.me/theorems/e2c68c9a-d41a-418b-8a12-8824eea41717
-- title:
--   Estimate: height pos
-- statement:
--   The Estimate construction uses the height pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Estimate.lean#L31-L33
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Estimate.lean#L31-L33

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

theorem Autoconvolutions.Estimate.height_pos (n s : ℕ) : 0 < height n s := by sorry
