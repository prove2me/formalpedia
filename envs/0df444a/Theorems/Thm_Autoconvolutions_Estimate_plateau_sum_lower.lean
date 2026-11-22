-- Prove2me | Theorems.Thm_Autoconvolutions_Estimate_plateau_sum_lower
-- name    : Autoconvolutions.Estimate.plateau_sum_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:53.17387+00:00
-- url     : https://prove2.me/theorems/93e5bcf9-3d7d-47f5-99c5-7bcdd1e208f3
-- title:
--   Estimate: plateau sum lower
-- statement:
--   Sum the contributions of the good plateaus, after lowering one copy of
--   their height to the common minimum `A_0`.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Estimate.lean#L73-L91
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Estimate.lean#L73-L91

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

theorem Autoconvolutions.Estimate.plateau_sum_lower {r b n K : ℕ} (hn : 0 < n) (hK : K ≤ n)
    (hb : 8*n^3 ≤ b) (hbr : b ≤ r) :
    height n 0 * (1-1/(n:ℝ)) * ((r:ℝ)*b)^(2*n) *
      (∑ s ∈ range (K+1), (s:ℝ) * ((b:ℝ)/r)^s) ≤
    ∑ s ∈ range (K+1), (s:ℝ) * count n r b s * (height n s)^2 := by sorry
