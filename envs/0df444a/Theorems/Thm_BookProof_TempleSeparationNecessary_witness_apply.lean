-- Prove2me | Theorems.Thm_BookProof_TempleSeparationNecessary_witness_apply
-- name    : BookProof.TempleSeparationNecessary.witness_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:03:31.839243+00:00
-- url     : https://prove2.me/theorems/edf14a72-52f8-48f5-9deb-f2e57f7924a3
-- title:
--   `BookProof.TempleSeparationNecessary.witness_apply` (M : ℝ) (x y : E2) : witness M x y = ((-M : ℝ) : ℂ) • (y - (inner ℂ x y : ℂ) • x)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTempleSeparationNecessary`.
--
--   `BookProof.TempleSeparationNecessary.witness_apply` (M : ℝ) (x y : E2) : witness M x y = ((-M : ℝ) : ℂ) • (y - (inner ℂ x y : ℂ) • x)
--
--   Formalization note: Lean 4 identifier `BookProof.TempleSeparationNecessary.witness_apply`.

-- Generated from ChapterTempleSeparationNecessary.lean — theorem BookProof.TempleSeparationNecessary.witness_apply
import Definitions.Def_ChapterRitzCertificate
import Mathlib
import Definitions.Def_ChapterTempleSeparationNecessary
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow.FarisLavineLift
open BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData
open BookProof.TempleSeparationNecessary


noncomputable section


open BookProof.RitzCertificate

theorem BookProof.TempleSeparationNecessary.witness_apply (M : ℝ) (x y : E2) :
    witness M x y = ((-M : ℝ) : ℂ) • (y - (inner ℂ x y : ℂ) • x) := by sorry
