-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_contextAnchors_deleteSites
-- name    : DeciSigma1.Holes.Fresh.contextAnchors_deleteSites
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:47.613253+00:00
-- url     : https://prove2.me/theorems/a695d8b6-4809-4aba-b473-beaa2b984771
-- title:
--   Fresh: context Anchors delete Sites
-- statement:
--   After deleting separated valid sites, the level-`r` anchors (`1 ≤ r ≤ t + 1`) of the edited
--   text, for the markers of `W`, are exactly the images under the cut map of the original anchors
--   outside the deleted open intervals.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L268-L317
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L268-L317

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
variable {W : Fin k → List α}
variable {δ : ℕ} {cs : Finset ℕ}

theorem DeciSigma1.Holes.Fresh.contextAnchors_deleteSites {t r : ℕ} (hr1 : 1 ≤ r)
    (hr : r ≤ t + 1) (cs : Finset ℕ) : ∀ {x : List α}, StrictlySeparated δ cs →
    (∀ c ∈ cs, ValidDeletionSite W t x c δ) → ∀ e,
      e ∈ contextAnchors W r (deletePositions x (sitePositions δ cs)) ↔
        ∃ p ∈ contextAnchors W r x, Retained δ cs p ∧ retainedCount (sitePositions δ cs) p = e := by sorry
