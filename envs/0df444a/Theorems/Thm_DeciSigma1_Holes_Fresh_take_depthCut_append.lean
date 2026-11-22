-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_take_depthCut_append
-- name    : DeciSigma1.Holes.Fresh.take_depthCut_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:55:28.531332+00:00
-- url     : https://prove2.me/theorems/24fb1c6c-bda6-4cb9-8ae6-82abab54f725
-- title:
--   Fresh: take depth Cut append
-- statement:
--   The word up to the cut at depth `d`, followed by the last `d` lower blocks, is the word up to
--   the end of the upper occurrence.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L70-L89
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L70-L89

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

theorem DeciSigma1.Holes.Fresh.take_depthCut_append {t : ℕ} {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) {d : ℕ}
    (hd : d ≤ lowerBlockCount W t o) :
    (W o.1).take (depthCut W t o d) ++ ((reversedBlocks W t o).take d).reverse.flatten =
      (W o.1).take o.2.2 := by sorry
