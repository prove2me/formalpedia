-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_lowerLevelTypes_mem_choices
-- name    : DeciSigma1.Holes.Fresh.lowerLevelTypes_mem_choices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:36.851112+00:00
-- url     : https://prove2.me/theorems/f84d3c34-a1bd-406d-9d01-92c981e6d751
-- title:
--   Fresh: lower Level Types mem choices
-- statement:
--   The Fresh construction uses the lower Level Types mem choices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L324-L326
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L324-L326

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}
variable {S : Type} [Fintype S] [DecidableEq S] {T : Table α S k}

theorem DeciSigma1.Holes.Fresh.lowerLevelTypes_mem_choices (t : ℕ) (u : List α) (c : ℕ) :
    lowerLevelTypes W t u c ∈ lowerLevelTypeChoices W t := by sorry
