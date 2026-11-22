-- Prove2me | Theorems.Thm_Autoconvolutions_Parameters_tendsto_factorialRatio
-- name    : Autoconvolutions.Parameters.tendsto_factorialRatio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:42.756811+00:00
-- url     : https://prove2.me/theorems/5da8efef-2813-46d1-ab89-5438560ac3e1
-- title:
--   Parameters: tendsto factorial Ratio
-- statement:
--   For fixed K, the ratio of factorial heights A₀ / A₂ₖ tends to one as n grows.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Main.lean#L67-L81
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Main.lean#L67-L81

module
public import Definitions.Def_Autoconvolutions_Witness
public import Definitions.Def_Autoconvolutions_Coefficients
public import Definitions.Def_Autoconvolutions_GoodBlocks
public import Definitions.Def_Autoconvolutions_Bounds
public import Mathlib.Analysis.SpecificLimits.Normed
public import Definitions.Def_Autoconvolutions_Main
set_option autoImplicit true
@[expose] public section
public section
open Filter Finset Polynomial
open scoped BigOperators Topology
open Autoconvolutions Autoconvolutions.Parameters

theorem Autoconvolutions.Parameters.tendsto_factorialRatio (K : ℕ) :
    Tendsto (fun n : ℕ => factorialRatio (2*n) (2*K)) atTop (𝓝 1) := by sorry
