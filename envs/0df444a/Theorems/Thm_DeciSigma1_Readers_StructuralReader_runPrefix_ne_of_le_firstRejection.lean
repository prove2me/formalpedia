-- Prove2me | Theorems.Thm_DeciSigma1_Readers_StructuralReader_runPrefix_ne_of_le_firstRejection
-- name    : DeciSigma1.Readers.StructuralReader.runPrefix_ne_of_le_firstRejection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:49:27.576271+00:00
-- url     : https://prove2.me/theorems/e9f24cb4-062a-4b97-b821-b23589ebeb01
-- title:
--   Structural Reader: run Prefix ne of le first Rejection
-- statement:
--   On an eligible coordinate, two cuts `a < b ≤ firstRejection` whose suffixes are
--   comparable carry distinct states.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L627-L638
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L627-L638

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

theorem DeciSigma1.Readers.StructuralReader.runPrefix_ne_of_le_firstRejection {W : Fin k → List α} {i : Fin k} {a b : ℕ}
    (h : M.Eligible W i) (hab : a < b)
    (hb : b ≤ M.firstRejection W i) (hp : (W i).drop b <+: (W i).drop a) :
    M.runPrefix W i a ≠ M.runPrefix W i b := by sorry
