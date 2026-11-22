-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_mem_upperOccurrences_top
-- name    : DeciSigma1.Holes.Fresh.mem_upperOccurrences_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:06:27.775385+00:00
-- url     : https://prove2.me/theorems/60bae4ce-15c8-4502-aa3b-e6d76b1b37df
-- title:
--   Fresh: mem upper Occurrences top
-- statement:
--   At the top level the upper occurrences are the nonempty words.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L809-L820
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L809-L820

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

theorem DeciSigma1.Holes.Fresh.mem_upperOccurrences_top {o : Fin k × ℕ × ℕ} :
    o ∈ upperOccurrences W (topLevel W) ↔ W o.1 ≠ [] ∧ o.2.2 = (W o.1).length ∧ o.2.1 = 0 := by sorry
