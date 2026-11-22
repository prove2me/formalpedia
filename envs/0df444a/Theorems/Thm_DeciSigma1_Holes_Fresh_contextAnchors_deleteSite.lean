-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_contextAnchors_deleteSite
-- name    : DeciSigma1.Holes.Fresh.contextAnchors_deleteSite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:43.173906+00:00
-- url     : https://prove2.me/theorems/d17fd883-07f3-416a-847e-dbb8a450b749
-- title:
--   Fresh: context Anchors delete Site
-- statement:
--   After deleting a valid site, the level-`r` anchors (`1 ≤ r ≤ t + 1`) of the edited text,
--   for the markers of `W`, are exactly the images of the original ones: cuts `≤ c` stay and cuts
--   `≥ c + δ` move left by `δ`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L166-L237
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L166-L237

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

theorem DeciSigma1.Holes.Fresh.contextAnchors_deleteSite {t : ℕ} {x : List α} {c δ : ℕ}
    (hS : ValidDeletionSite W t x c δ) {r : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ t + 1) (e : ℕ) :
    e ∈ contextAnchors W r (x.take c ++ x.drop (c + δ)) ↔
      (e ≤ c ∧ e ∈ contextAnchors W r x) ∨ (c ≤ e ∧ e + δ ∈ contextAnchors W r x) := by sorry
