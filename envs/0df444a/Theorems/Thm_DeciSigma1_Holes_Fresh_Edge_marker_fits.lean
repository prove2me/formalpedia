-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_marker_fits
-- name    : DeciSigma1.Holes.Fresh.Edge.marker_fits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:25.808682+00:00
-- url     : https://prove2.me/theorems/87b2d962-a64c-47f9-850d-11ce60f0b733
-- title:
--   Edge: marker fits
-- statement:
--   By the deletion margin, every marker recorded in a label lies inside the common edge
--   text.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L153-L201
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L153-L201

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

theorem DeciSigma1.Holes.Fresh.Edge.marker_fits (hfr : ∀ i, T.Fresh W i)
    {t : ℕ} (e : Edge W t) {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t)
    (hth : e.TraversedBy o) {p : ℕ} (hp0 : 0 < p)
    (hp : p + deletionMargin k (Fintype.card S) ≤ e.endDepth)
    {r : ℕ} (hr : 1 ≤ r) (hrt : r ≤ t) {m : Fin k} (hm : m ∈ active W r)
    (hs : marker W r m <:+ (W o.1).take (depthCut W t o p)) :
    (marker W r m).length ≤ depthCut W t o p - depthCut W t o e.endDepth := by sorry
