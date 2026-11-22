-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_labels_eq_of_jointLabel
-- name    : DeciSigma1.Holes.Fresh.labels_eq_of_jointLabel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:39.380679+00:00
-- url     : https://prove2.me/theorems/4c04b7df-2305-4782-9a4c-9bc976c49737
-- title:
--   Fresh: labels eq of joint Label
-- statement:
--   Equal joint labels at two depths give equal labels at these depths in every traversing
--   occurrence.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L343-L353
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L343-L353

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

theorem DeciSigma1.Holes.Fresh.labels_eq_of_jointLabel (hfr : ∀ i, T.Fresh W i)
    {t : ℕ} (e : Edge W t) {i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    (hi' : i + deletionMargin k (Fintype.card S) ≤ e.endDepth)
    (hj' : j + deletionMargin k (Fintype.card S) ≤ e.endDepth)
    (heq : jointLabel T e j = jointLabel T e i)
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) (hth : e.TraversedBy o) :
    label T W t o.1 (depthCut W t o j) = label T W t o.1 (depthCut W t o i) := by sorry
