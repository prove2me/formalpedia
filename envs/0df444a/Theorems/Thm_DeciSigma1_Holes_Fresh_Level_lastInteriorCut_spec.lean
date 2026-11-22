-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_Level_lastInteriorCut_spec
-- name    : DeciSigma1.Holes.Fresh.Level.lastInteriorCut_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:16.41593+00:00
-- url     : https://prove2.me/theorems/71decee2-2b6e-4533-bef0-10c19f513311
-- title:
--   Level: last Interior Cut spec
-- statement:
--   The Level construction uses the last Interior Cut spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L183-L195
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L183-L195

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
open DeciSigma1.Holes.Fresh.Level
variable [DecidableEq α] (L : Level α k)
variable {L}

theorem DeciSigma1.Holes.Fresh.Level.lastInteriorCut_spec {x : List α} (h : ∃ e ∈ L.markerEndCuts x, e < x.length) :
    L.lastInteriorCut x ∈ L.markerEndCuts x ∧ L.lastInteriorCut x < x.length ∧
      ∀ e ∈ L.markerEndCuts x, e < x.length → e ≤ L.lastInteriorCut x := by sorry
