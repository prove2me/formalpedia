-- Prove2me | Theorems.Thm_Autoconvolutions_Estimate_lower_le_block_fraction
-- name    : Autoconvolutions.Estimate.lower_le_block_fraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:59.628768+00:00
-- url     : https://prove2.me/theorems/36b75d13-ba42-442b-8ba8-a96c4b35f633
-- title:
--   Estimate: lower le block fraction
-- statement:
--   A version for the geometric block lemma: the right-hand side here is its
--   finite lower bound for the genuine autoconvolution ratio.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Estimate.lean#L142-L150
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Estimate.lean#L142-L150

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

theorem Autoconvolutions.Estimate.lower_le_block_fraction {r b n K : ℕ} (hn : 0 < n) (hK : K ≤ n)
    (hb : 8*n^3 ≤ b) (hbr : b ≤ r) {eval : ℝ}
    (heval : eval = ((r:ℝ)*b)^n * ∑ s ∈ range (K+1), ((b:ℝ)/r)^s) :
    (1-1/(n:ℝ)) * Parameters.factorialRatio (2*n) (2*K) *
      Parameters.geomRatio ((b:ℝ)/r) K ≤
      (∑ s ∈ range (K+1), (s:ℝ)*count n r b s*(height n s)^2) /
        (eval^2 * height n (2*K)) := by sorry
