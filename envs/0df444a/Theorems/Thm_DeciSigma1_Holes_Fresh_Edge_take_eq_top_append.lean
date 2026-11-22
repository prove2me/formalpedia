-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_take_eq_top_append
-- name    : DeciSigma1.Holes.Fresh.Edge.take_eq_top_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:51:30.493832+00:00
-- url     : https://prove2.me/theorems/531793a7-104e-4008-9455-b11efa0e5734
-- title:
--   Edge: take eq top append
-- statement:
--   The Edge construction uses the take eq top append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L100-L122
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L100-L122

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

theorem DeciSigma1.Holes.Fresh.Edge.take_eq_top_append {t : ℕ} (e : Edge W t)
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) (hth : e.TraversedBy o)
    {p : ℕ} (hp : p ≤ e.endDepth) :
    (W o.1).take (depthCut W t o p) =
      (W o.1).take (depthCut W t o e.endDepth) ++ edgePrefix e p := by sorry
