-- Prove2me | Theorems.Thm_Autoconvolutions_Blocks_coeff_cap
-- name    : Autoconvolutions.Blocks.coeff_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:45.60113+00:00
-- url     : https://prove2.me/theorems/95e43e09-3d4a-41ae-a586-0d3df1ebf27e
-- title:
--   Blocks: coeff cap
-- statement:
--   Every coefficient of F² is bounded by the factorial height at the last level.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Coefficients.lean#L79-L104
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Coefficients.lean#L79-L104

module
public import Definitions.Def_Autoconvolutions_BlockExpansion
public import Definitions.Def_Autoconvolutions_Occupancy
public import Definitions.Def_Autoconvolutions_Estimate
public import Definitions.Def_Autoconvolutions_Flat
public import Definitions.Def_Autoconvolutions_Coefficients
set_option autoImplicit true
@[expose] public section
public section
open Finset Polynomial
open scoped BigOperators
open Autoconvolutions Autoconvolutions.Blocks

theorem Autoconvolutions.Blocks.coeff_cap {m n K D : ℕ} (I J : Finset (Fin m))
    (hd : Disjoint I J) (hK : K < n) (hD : 4*n < D) (x : ℕ) :
    ((Construction.family Flat.P (gen D I) (gen D J) n K)^2).coeff x ≤
      Estimate.height n (2*K) := by sorry
