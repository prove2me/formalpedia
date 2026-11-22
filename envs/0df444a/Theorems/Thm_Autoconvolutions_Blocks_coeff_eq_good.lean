-- Prove2me | Theorems.Thm_Autoconvolutions_Blocks_coeff_eq_good
-- name    : Autoconvolutions.Blocks.coeff_eq_good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:44.800111+00:00
-- url     : https://prove2.me/theorems/9e1e41dd-ac5b-4ad5-a3a9-a6d9d25509a9
-- title:
--   Blocks: coeff eq good
-- statement:
--   Every low digit in a good block, including its right endpoint, gives the same
--   coefficient. In the piecewise linear convolution the plateau thus has length s.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Coefficients.lean#L108-L127
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Coefficients.lean#L108-L127

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

theorem Autoconvolutions.Blocks.coeff_eq_good {m n K D s : ℕ} (I J : Finset (Fin m))
    (hd : Disjoint I J) (hK : K < n) (hD : 4*n < D) (hs : s ≤ K)
    {a b : Fin m → ℕ} (ha : a ∈ goodVectors I (2*n-s)) (hb : b ∈ goodVectors J (2*n+s))
    (h : ℕ) (hh : h ≤ s) :
    ((Construction.family Flat.P (gen D I) (gen D J) n K)^2).coeff (key D a b h) =
      Estimate.height n s := by sorry
