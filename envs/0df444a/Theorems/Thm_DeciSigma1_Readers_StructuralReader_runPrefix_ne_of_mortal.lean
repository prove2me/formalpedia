-- Prove2me | Theorems.Thm_DeciSigma1_Readers_StructuralReader_runPrefix_ne_of_mortal
-- name    : DeciSigma1.Readers.StructuralReader.runPrefix_ne_of_mortal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:52:38.290728+00:00
-- url     : https://prove2.me/theorems/2769df9c-dce4-4812-9478-566acfcbf4e5
-- title:
--   Structural Reader: run Prefix ne of mortal
-- statement:
--   On an eligible coordinate with a mortal endpoint, two cuts `a < b` whose suffixes are
--   comparable (the suffix after `b` is a prefix of the suffix after `a`) carry distinct states.
--   The empty suffix `b = |W i|` is included.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L614-L623
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L614-L623

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

theorem DeciSigma1.Readers.StructuralReader.runPrefix_ne_of_mortal {W : Fin k → List α} {i : Fin k} {a b : ℕ}
    (h : M.Eligible W i) (hm : ¬ M.Immortal (M.endState W i)) (hab : a < b) (hb : b ≤ (W i).length)
    (hp : (W i).drop b <+: (W i).drop a) : M.runPrefix W i a ≠ M.runPrefix W i b := by sorry
