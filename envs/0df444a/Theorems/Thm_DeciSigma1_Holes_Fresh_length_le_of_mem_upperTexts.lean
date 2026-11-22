-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_length_le_of_mem_upperTexts
-- name    : DeciSigma1.Holes.Fresh.length_le_of_mem_upperTexts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:06:49.590811+00:00
-- url     : https://prove2.me/theorems/f6ee765e-9e92-4364-8031-d67c6b3da65b
-- title:
--   Fresh: length le of mem upper Texts
-- statement:
--   Expanding through all levels bounds the length of every upper block.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L924-L955
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L924-L955

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

theorem DeciSigma1.Holes.Fresh.length_le_of_mem_upperTexts (hsl : IsMinimalFresh T W) (t : ℕ) (ht : t ≤ topLevel W)
    {z : List α} (hz : z ∈ upperTexts W t) :
    z.length ≤ expansionBlockCountBound k (Fintype.card S) ^ (t + 1) := by sorry
