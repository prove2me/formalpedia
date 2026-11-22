-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_getElem_reversedBlocks
-- name    : DeciSigma1.Holes.Fresh.getElem_reversedBlocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:20.415174+00:00
-- url     : https://prove2.me/theorems/5853d537-beaa-4c9d-ac43-de47c94a87cf
-- title:
--   Fresh: get Elem reversed Blocks
-- statement:
--   The Fresh construction uses the get Elem reversed Blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L408-L412
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L408-L412

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}

theorem DeciSigma1.Holes.Fresh.getElem_reversedBlocks (W : Fin k → List α) (t : ℕ) (o : Fin k × ℕ × ℕ) {d : ℕ}
    (hd : d < (reversedBlocks W t o).length) :
    (reversedBlocks W t o)[d] =
      ((W o.1).drop (depthCut W t o (d + 1))).take (depthCut W t o d - depthCut W t o (d + 1)) := by sorry
