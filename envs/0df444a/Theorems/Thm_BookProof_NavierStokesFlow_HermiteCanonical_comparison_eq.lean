-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteCanonical_comparison_eq
-- name    : BookProof.NavierStokesFlow.HermiteCanonical.comparison_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:13:10.671858+00:00
-- url     : https://prove2.me/theorems/15d79694-079a-4321-8d94-a4c2f542f224
-- title:
--   (hκ : 0 ≤ κ) : (lpFiniteModes ℕ).subtype.comp ((mom κ).comp (mom κ) + (drift κ).comp (drift κ) + LinearMap.id) = (diagMax (oscSymbol κ)).comp (Submodule.inclusion...
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.HermiteCanonical.comparison_eq` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesHermiteCanonical.lean — theorem BookProof.NavierStokesFlow.HermiteCanonical.comparison_eq
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.HermiteFarisLavine
open BookProof.NavierStokesFlow.IkebeKato
























variable {κ : ℝ}

theorem BookProof.NavierStokesFlow.HermiteCanonical.comparison_eq (hκ : 0 ≤ κ) :
    (lpFiniteModes ℕ).subtype.comp
        ((mom κ).comp (mom κ) + (drift κ).comp (drift κ) + LinearMap.id)
      = (diagMax (oscSymbol κ)).comp
        (Submodule.inclusion (finiteModes_le_maxDom (oscSymbol κ))) := by sorry
