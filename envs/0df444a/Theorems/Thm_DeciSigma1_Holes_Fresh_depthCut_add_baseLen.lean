-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_depthCut_add_baseLen
-- name    : DeciSigma1.Holes.Fresh.depthCut_add_baseLen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:02:32.089786+00:00
-- url     : https://prove2.me/theorems/30951996-5ce3-4bca-8087-a376935f328e
-- title:
--   Fresh: depth Cut add base Len
-- statement:
--   The cut at depth `d` is the end minus the total length of the last `d` lower blocks.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L458-L475
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L458-L475

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

theorem DeciSigma1.Holes.Fresh.depthCut_add_baseLen {W : Fin k → List α} {t : ℕ}
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) {d : ℕ} (hd : d ≤ lowerBlockCount W t o) :
    depthCut W t o d + firstBlocksLength (reversedBlocks W t o) d = o.2.2 := by sorry
