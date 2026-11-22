-- Prove2me | Theorems.Thm_Autoconvolutions_Construction_witness_nonneg
-- name    : Autoconvolutions.Construction.witness_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:42.668947+00:00
-- url     : https://prove2.me/theorems/58fc4ea0-9d4d-4a7e-ac3d-1d80a403239b
-- title:
--   Construction: witness nonneg
-- statement:
--   The Construction construction uses the witness nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Witness.lean#L27-L34
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Witness.lean#L27-L34

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

theorem Autoconvolutions.Construction.witness_nonneg {m n K D : ℕ} (I J : Finset (Fin m)) (k : ℕ) :
    0 ≤ (witness D n K I J).coeff k := by sorry
