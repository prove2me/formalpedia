-- Prove2me | Theorems.Thm_Autoconvolutions_Construction_witness_ratio_lower
-- name    : Autoconvolutions.Construction.witness_ratio_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:45.858869+00:00
-- url     : https://prove2.me/theorems/0852cb54-a5a5-40e7-8c83-bd190b22e5ee
-- title:
--   Construction: witness ratio lower
-- statement:
--   Equation (lower), for the actual step function of the constructed polynomial.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Main.lean#L26-L60
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Main.lean#L26-L60

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
open Autoconvolutions Autoconvolutions.Construction

theorem Autoconvolutions.Construction.witness_ratio_lower {m n K D : ℕ} (I J : Finset (Fin m))
    (hd : Disjoint I J) (hK : K < n) (hD : 4*n < D)
    (hJ : 8*n^3 ≤ J.card) (hIJ : J.card ≤ I.card) :
    let F := witness D n K I J
    (1 - 1/(n:ℝ)) * Parameters.factorialRatio (2*n) (2*K) *
      Parameters.geomRatio ((J.card:ℝ) / I.card) K ≤
      ratio (step F.natDegree (Polynomial.toFn (F.natDegree+1) F)) := by sorry
