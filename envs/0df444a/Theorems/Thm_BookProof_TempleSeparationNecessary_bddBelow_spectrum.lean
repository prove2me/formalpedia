-- Prove2me | Theorems.Thm_BookProof_TempleSeparationNecessary_bddBelow_spectrum
-- name    : BookProof.TempleSeparationNecessary.bddBelow_spectrum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:05:08.417977+00:00
-- url     : https://prove2.me/theorems/fb8d309e-f038-4f91-8705-f71cf8e5a647
-- title:
--   `BookProof.TempleSeparationNecessary.bddBelow_spectrum` (A : E2 →L[ℂ] E2) : BddBelow (spectrum ℝ A)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTempleSeparationNecessary`.
--
--   `BookProof.TempleSeparationNecessary.bddBelow_spectrum` (A : E2 →L[ℂ] E2) : BddBelow (spectrum ℝ A)
--
--   Formalization note: Lean 4 identifier `BookProof.TempleSeparationNecessary.bddBelow_spectrum`.

-- Generated from ChapterTempleSeparationNecessary.lean — theorem BookProof.TempleSeparationNecessary.bddBelow_spectrum
import Definitions.Def_ChapterRitzCertificate
import Mathlib
import Definitions.Def_ChapterTempleSeparationNecessary
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow.FarisLavineLift
open BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData
open BookProof.TempleSeparationNecessary


noncomputable section


open BookProof.RitzCertificate

theorem BookProof.TempleSeparationNecessary.bddBelow_spectrum (A : E2 →L[ℂ] E2) : BddBelow (spectrum ℝ A) := by sorry
