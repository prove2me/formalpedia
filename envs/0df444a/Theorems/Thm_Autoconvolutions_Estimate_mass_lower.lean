-- Prove2me | Theorems.Thm_Autoconvolutions_Estimate_mass_lower
-- name    : Autoconvolutions.Estimate.mass_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:51.770537+00:00
-- url     : https://prove2.me/theorems/9570e82d-5708-454d-ad2c-f46f470d0060
-- title:
--   Estimate: mass lower
-- statement:
--   The geometric mass bound with the alphabet sizes and factorial height
--   used by the polynomial construction.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Estimate.lean#L63-L69
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Estimate.lean#L63-L69

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

theorem Autoconvolutions.Estimate.mass_lower {r b n s : ℕ} (hn : 0 < n) (hb : 8*n^3 ≤ b) (hbr : b ≤ r)
    (hs : s ≤ 2*n) :
    (1-1/(n:ℝ)) * ((r:ℝ)*b)^(2*n) * ((b:ℝ)/r)^s ≤ count n r b s * height n s := by sorry
