-- Prove2me | Theorems.Thm_Autoconvolutions_Estimate_count_nonneg
-- name    : Autoconvolutions.Estimate.count_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:51.490829+00:00
-- url     : https://prove2.me/theorems/f55fc954-69f2-4dc0-9465-5f1a4f6eaf6d
-- title:
--   Estimate: count nonneg
-- statement:
--   The Estimate construction uses the count nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Estimate.lean#L35-L37
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Estimate.lean#L35-L37

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

theorem Autoconvolutions.Estimate.count_nonneg (n r b s : ℕ) : 0 ≤ count n r b s := by sorry
