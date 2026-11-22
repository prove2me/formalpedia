-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_retainedCount_surj
-- name    : DeciSigma1.Holes.Tail.retainedCount_surj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:59:17.244407+00:00
-- url     : https://prove2.me/theorems/febd8d8e-5bac-49f7-a218-afe9f9c10a27
-- title:
--   Tail: retained Count surj
-- statement:
--   Every position of the edited word is the image of a retained original position.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Compression.lean#L59-L73
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Compression.lean#L59-L73

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Bound
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RunCovers
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Compression
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}

theorem DeciSigma1.Holes.Tail.retainedCount_surj {a p' : ℕ} (h : p' < retainedCount D a) :
    ∃ p < a, p ∉ D ∧ retainedCount D p = p' := by sorry
