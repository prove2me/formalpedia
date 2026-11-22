-- Prove2me | Theorems.Thm_DeciSigma1_Readers_StructuralReader_fresh_of_mortal
-- name    : DeciSigma1.Readers.StructuralReader.fresh_of_mortal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:52:32.406576+00:00
-- url     : https://prove2.me/theorems/22a6b471-99c9-4703-b0e6-c0494942e05e
-- title:
--   Structural Reader: fresh of mortal
-- statement:
--   An eligible coordinate with a mortal endpoint is fresh.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L588-L591
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L588-L591

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

theorem DeciSigma1.Readers.StructuralReader.fresh_of_mortal [DecidableEq S] {W : Fin k → List α} {i : Fin k} (h : M.Eligible W i)
    (hm : ¬ M.Immortal (M.endState W i)) : M.Fresh W i := by sorry
