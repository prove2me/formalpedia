-- Prove2me | Theorems.Thm_DeciSigma1_Readers_StructuralReader_rejected_along
-- name    : DeciSigma1.Readers.StructuralReader.rejected_along
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:31.439796+00:00
-- url     : https://prove2.me/theorems/7d8c2a44-366e-40e4-b53e-a2bd143f82b1
-- title:
--   Structural Reader: rejected along
-- statement:
--   Along a live word read from a rejected state every state is rejected.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L454-L466
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L454-L466

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Finset.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Readers
open DeciSigma1.Automata
variable {α S : Type} {k : ℕ}
open Table
open DeciSigma1.Readers.StructuralReader
variable (M : StructuralReader α S k)
variable {M}

theorem DeciSigma1.Readers.StructuralReader.rejected_along {q : S} {u : List α} (hq : M.rejected q = true) (hl : M.LiveAlong q u) :
    ∀ a ≤ u.length, M.rejected (runFrom M.step q (u.take a)) = true := by sorry
