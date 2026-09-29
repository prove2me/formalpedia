-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteCanonical_sqrt_half_mul_inv
-- name    : BookProof.NavierStokesFlow.HermiteCanonical.sqrt_half_mul_inv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:56:34.896934+00:00
-- url     : https://prove2.me/theorems/06917044-0b0c-4add-adee-66730e1ea954
-- title:
--   (hκ : 0 < κ) : (Real.sqrt (κ / 2) : ℂ) * ((1 / Real.sqrt (2 * κ) : ℝ) : ℂ) = 1 / 2
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.HermiteCanonical.sqrt_half_mul_inv` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesHermiteCanonical.lean — theorem BookProof.NavierStokesFlow.HermiteCanonical.sqrt_half_mul_inv
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.HermiteFarisLavine
























variable {κ : ℝ}

theorem BookProof.NavierStokesFlow.HermiteCanonical.sqrt_half_mul_inv (hκ : 0 < κ) :
    (Real.sqrt (κ / 2) : ℂ) * ((1 / Real.sqrt (2 * κ) : ℝ) : ℂ) = 1 / 2 := by sorry
