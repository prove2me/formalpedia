-- Prove2me | Theorems.Thm_Autoconvolutions_Estimate_norm_ratio_lower
-- name    : Autoconvolutions.Estimate.norm_ratio_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:54.689574+00:00
-- url     : https://prove2.me/theorems/5b8d621c-c983-483e-937d-e6ac056c128c
-- title:
--   Estimate: norm ratio lower
-- statement:
--   Equation (lower) from the actual three norm bounds.
--   `square` denotes the square of the L² norm, `one` the L¹ norm,
--   and `peak` the L∞ norm. All assumptions are explicit.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Estimate.lean#L96-L138
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Estimate.lean#L96-L138

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

theorem Autoconvolutions.Estimate.norm_ratio_lower {r b n K : ℕ} (hn : 0 < n) (hK : K ≤ n)
    (hb : 8*n^3 ≤ b) (hbr : b ≤ r) {square one peak : ℝ}
    (hOne : one = (((r:ℝ)*b)^n * ∑ s ∈ range (K+1), ((b:ℝ)/r)^s)^2)
    (hPeakPos : 0 < peak) (hPeak : peak ≤ height n (2*K))
    (hSq : (∑ s ∈ range (K+1), (s:ℝ)*count n r b s*(height n s)^2) ≤ square) :
    (1-1/(n:ℝ)) * Parameters.factorialRatio (2*n) (2*K) *
      Parameters.geomRatio ((b:ℝ)/r) K ≤ square/(one*peak) := by sorry
