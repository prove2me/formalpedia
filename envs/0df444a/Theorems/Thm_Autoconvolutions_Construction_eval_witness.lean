-- Prove2me | Theorems.Thm_Autoconvolutions_Construction_eval_witness
-- name    : Autoconvolutions.Construction.eval_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:40.731518+00:00
-- url     : https://prove2.me/theorems/62c48f76-df8f-4c14-b716-95dfd6c727ab
-- title:
--   Construction: eval witness
-- statement:
--   The evaluation of the witness at one is the mass before autoconvolution.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Witness.lean#L20-L25
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Witness.lean#L20-L25

module
public import Definitions.Def_Autoconvolutions_BlockExpansion
public import Definitions.Def_Autoconvolutions_Estimate
public import Definitions.Def_Autoconvolutions_Flat
public import Definitions.Def_Autoconvolutions_PolyStep
public import Definitions.Def_Autoconvolutions_Witness
set_option autoImplicit true
@[expose] public section
public section
open Finset Polynomial
open scoped BigOperators
open Autoconvolutions Autoconvolutions.Construction

theorem Autoconvolutions.Construction.eval_witness {m n K D : ℕ} (I J : Finset (Fin m)) (hK : K ≤ n) (hI : 0 < I.card) :
    (witness D n K I J).eval 1 =
    ((I.card : ℝ) * J.card)^n * ∑ i ∈ range (K+1), ((J.card : ℝ)/I.card)^i := by sorry
