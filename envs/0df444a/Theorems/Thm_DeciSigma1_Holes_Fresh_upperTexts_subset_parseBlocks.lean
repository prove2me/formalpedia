-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_upperTexts_subset_parseBlocks
-- name    : DeciSigma1.Holes.Fresh.upperTexts_subset_parseBlocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:06:20.193035+00:00
-- url     : https://prove2.me/theorems/a4c0b02d-6ace-416c-bf1e-0805a36f1f03
-- title:
--   Fresh: upper Texts subset parse Blocks
-- statement:
--   The text of every upper block of level `t + 1` is a lower block in the parse of some upper
--   block of level `t + 2`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L708-L750
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L708-L750

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

theorem DeciSigma1.Holes.Fresh.upperTexts_subset_parseBlocks (t : ℕ) :
    upperTexts W t ⊆ (upperParses W (t + 1)).biUnion List.toFinset := by sorry
