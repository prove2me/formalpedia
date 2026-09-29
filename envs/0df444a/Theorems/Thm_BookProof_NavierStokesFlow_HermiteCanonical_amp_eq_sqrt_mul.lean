-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteCanonical_amp_eq_sqrt_mul
-- name    : BookProof.NavierStokesFlow.HermiteCanonical.amp_eq_sqrt_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:28:16.226796+00:00
-- url     : https://prove2.me/theorems/05479f96-f2c4-499c-984d-468e96ec8512
-- title:
--   (κ : ℝ) (n : ℕ) : amp κ n = (κ / 2) * (Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 2))
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.HermiteCanonical.amp_eq_sqrt_mul` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesHermiteCanonical.lean — theorem BookProof.NavierStokesFlow.HermiteCanonical.amp_eq_sqrt_mul
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.HermiteFarisLavine
























variable {κ : ℝ}

theorem BookProof.NavierStokesFlow.HermiteCanonical.amp_eq_sqrt_mul (κ : ℝ) (n : ℕ) :
    amp κ n = (κ / 2) * (Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 2)) := by sorry
