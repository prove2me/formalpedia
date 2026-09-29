-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteCanonical_canonical_essentiallySelfAdjointOn_core
-- name    : BookProof.NavierStokesFlow.HermiteCanonical.canonical_essentiallySelfAdjointOn_core
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:47:16.841358+00:00
-- url     : https://prove2.me/theorems/2b863f31-62ed-4520-90b9-a2877ec78919
-- title:
--   (hκ : 0 ≤ κ) : EssentiallySelfAdjointOn (lpFiniteModes ℕ) ((lpFiniteModes ℕ).subtype.comp (((1 : ℂ) / 2) • ((mom κ).comp (drift κ) + (drift κ).comp (mom κ))))
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.HermiteCanonical.canonical_essentiallySelfAdjointOn_core` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesHermiteCanonical.lean — theorem BookProof.NavierStokesFlow.HermiteCanonical.canonical_essentiallySelfAdjointOn_core
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.HermiteFarisLavine
























variable {κ : ℝ}

theorem BookProof.NavierStokesFlow.HermiteCanonical.canonical_essentiallySelfAdjointOn_core (hκ : 0 ≤ κ) :
    EssentiallySelfAdjointOn (lpFiniteModes ℕ)
      ((lpFiniteModes ℕ).subtype.comp
        (((1 : ℂ) / 2) • ((mom κ).comp (drift κ) + (drift κ).comp (mom κ)))) := by sorry
