-- Prove2me | Theorems.Thm_BookProof_HermiteExpWall_integral_psi_sq
-- name    : BookProof.HermiteExpWall.integral_psi_sq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:09:54.781594+00:00
-- url     : https://prove2.me/theorems/116945ff-cc6c-4118-ad7b-7eaecc3e7076
-- title:
--   `BookProof.HermiteExpWall.integral_psi_sq` (N : ℕ) : ∫ x : ℝ, psi N x ^ 2 = gaussMoment (2 * N)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteExpWall`.
--
--   `BookProof.HermiteExpWall.integral_psi_sq` (N : ℕ) : ∫ x : ℝ, psi N x ^ 2 = gaussMoment (2 * N)
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteExpWall.integral_psi_sq`.

-- Generated from ChapterHermiteExpWall.lean — theorem BookProof.HermiteExpWall.integral_psi_sq
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQgHermiteCore
import Mathlib
import Definitions.Def_ChapterHermiteExpWall
import Definitions.Def_ChapterGhostField
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterHermiteProductCore
open BookProof.GhostField
open BookProof.HermiteCore
open BookProof.HermiteProductCore
open BookProof.HermiteExpWall



open MeasureTheory Polynomial
open BookProof.HermiteCore BookProof.Starobinsky BookProof.QgHermiteCore
open BookProof.HermiteProductCore

noncomputable section

theorem BookProof.HermiteExpWall.integral_psi_sq (N : ℕ) : ∫ x : ℝ, psi N x ^ 2 = gaussMoment (2 * N) := by sorry
