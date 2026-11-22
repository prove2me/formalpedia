-- Prove2me | Theorems.Thm_DeciSigma1_Readers_StructuralReader_immortal_of_not_fresh
-- name    : DeciSigma1.Readers.StructuralReader.immortal_of_not_fresh
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:40.35308+00:00
-- url     : https://prove2.me/theorems/8afaf38f-9261-4323-bcd0-7cea79bb0b6a
-- title:
--   Structural Reader: immortal of not fresh
-- statement:
--   An eligible coordinate that is not fresh ends on a live cycle, so its endpoint is
--   immortal.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L576-L585
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L576-L585

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

theorem DeciSigma1.Readers.StructuralReader.immortal_of_not_fresh [DecidableEq S] {W : Fin k → List α} {i : Fin k}
    (h : M.Eligible W i) (hf : ¬ M.Fresh W i) : M.Immortal (M.endState W i) := by sorry
