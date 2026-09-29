-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteCanonical_sqrt_half_sq
-- name    : BookProof.NavierStokesFlow.HermiteCanonical.sqrt_half_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:33:59.562866+00:00
-- url     : https://prove2.me/theorems/a34d0f67-d761-4624-8184-4be0d55cc023
-- title:
--   (hκ : 0 ≤ κ) : (Real.sqrt (κ / 2) : ℂ) * (Real.sqrt (κ / 2) : ℂ) = (κ : ℂ) / 2
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.HermiteCanonical.sqrt_half_sq` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesHermiteCanonical.lean — theorem BookProof.NavierStokesFlow.HermiteCanonical.sqrt_half_sq
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.HermiteFarisLavine
























variable {κ : ℝ}

theorem BookProof.NavierStokesFlow.HermiteCanonical.sqrt_half_sq (hκ : 0 ≤ κ) :
    (Real.sqrt (κ / 2) : ℂ) * (Real.sqrt (κ / 2) : ℂ) = (κ : ℂ) / 2 := by sorry
