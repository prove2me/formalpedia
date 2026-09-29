-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteCanonical_sqrt_mul_sqrt
-- name    : BookProof.NavierStokesFlow.HermiteCanonical.sqrt_mul_sqrt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:57:22.13384+00:00
-- url     : https://prove2.me/theorems/d3a4d29e-44b8-47eb-90c7-6399dfcab3a7
-- title:
--   (r : ℝ) (hr : 0 ≤ r) : (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) = (r : ℂ)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.HermiteCanonical.sqrt_mul_sqrt` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesHermiteCanonical.lean — theorem BookProof.NavierStokesFlow.HermiteCanonical.sqrt_mul_sqrt
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.HermiteFarisLavine

theorem BookProof.NavierStokesFlow.HermiteCanonical.sqrt_mul_sqrt (r : ℝ) (hr : 0 ≤ r) : (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) = (r : ℂ) := by sorry
