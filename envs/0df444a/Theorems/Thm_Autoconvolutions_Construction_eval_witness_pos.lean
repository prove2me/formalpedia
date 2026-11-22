-- Prove2me | Theorems.Thm_Autoconvolutions_Construction_eval_witness_pos
-- name    : Autoconvolutions.Construction.eval_witness_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:38.206935+00:00
-- url     : https://prove2.me/theorems/82ad77f4-72a7-4e5d-b2d2-f0227bbca75f
-- title:
--   Construction: eval witness pos
-- statement:
--   The Construction construction uses the eval witness pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Witness.lean#L36-L42
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Witness.lean#L36-L42

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

theorem Autoconvolutions.Construction.eval_witness_pos {m n K D : ℕ} (I J : Finset (Fin m))
    (hK : K ≤ n) (hI : 0 < I.card) (hJ : 0 < J.card) : 0 < (witness D n K I J).eval 1 := by sorry
