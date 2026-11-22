-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_label_local
-- name    : DeciSigma1.Holes.Fresh.label_local
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:34.592838+00:00
-- url     : https://prove2.me/theorems/dd65c566-011a-4426-a9d4-e1f8d6ce8d74
-- title:
--   Fresh: label local
-- statement:
--   The label of the cut at a given depth of a traversing occurrence is determined by marker
--   texts common to all traversing occurrences, a common state map, and the state of the occurrence
--   at the top of the edge.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L260-L293
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L260-L293

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

theorem DeciSigma1.Holes.Fresh.label_local (hfr : ∀ i, T.Fresh W i)
    {t : ℕ} (e : Edge W t) {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t)
    (hth : e.TraversedBy o) {p : ℕ} (hp0 : 0 < p)
    (hp : p + deletionMargin k (Fintype.card S) ≤ e.endDepth) :
    label T W t o.1 (depthCut W t o p) =
      (lowerLevelTypes W t (edgePrefix e p) (edgePrefix e p).length,
        edgeMap T e p (T.runPrefix W o.1 (depthCut W t o e.endDepth))) := by sorry
