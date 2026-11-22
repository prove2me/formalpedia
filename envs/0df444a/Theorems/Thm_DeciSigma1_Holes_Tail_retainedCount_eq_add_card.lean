-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_retainedCount_eq_add_card
-- name    : DeciSigma1.Holes.Tail.retainedCount_eq_add_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:59:33.810872+00:00
-- url     : https://prove2.me/theorems/91f155ca-970a-4f7a-a1fb-ea573fc22b28
-- title:
--   Tail: retained Count eq add card
-- statement:
--   The retained positions of `[s, e)` count `retainedCount e - retainedCount s`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Compression.lean#L76-L89
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Compression.lean#L76-L89

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

theorem DeciSigma1.Holes.Tail.retainedCount_eq_add_card {s e : ℕ} (h : s ≤ e) :
    retainedCount D e = retainedCount D s + ((Finset.Ico s e).filter (· ∉ D)).card := by sorry
