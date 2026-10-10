-- Prove2me | Theorems.Thm_BookProof_HermiteExpWall_l2_psi_sq
-- name    : BookProof.HermiteExpWall.l2_psi_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:10:26.326903+00:00
-- url     : https://prove2.me/theorems/fd431229-fa92-41d5-99d5-e97c72eab11c
-- title:
--   `BookProof.HermiteExpWall.l2_psi_sq` (N : ℕ) : l2 (psi N) ^ 2 = gaussMoment (2 * N)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteExpWall`.
--
--   `BookProof.HermiteExpWall.l2_psi_sq` (N : ℕ) : l2 (psi N) ^ 2 = gaussMoment (2 * N)
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteExpWall.l2_psi_sq`.

-- Generated from ChapterHermiteExpWall.lean — theorem BookProof.HermiteExpWall.l2_psi_sq
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQgHermiteCore
import Mathlib
import Definitions.Def_ChapterHermiteExpWall
import Definitions.Def_ChapterGhostField
import Definitions.Def_ChapterHermiteProductCore
open BookProof.GhostField
open BookProof.HermiteProductCore
open BookProof.HermiteExpWall



open MeasureTheory Polynomial
open BookProof.HermiteCore BookProof.Starobinsky BookProof.QgHermiteCore
open BookProof.HermiteProductCore

noncomputable section

theorem BookProof.HermiteExpWall.l2_psi_sq (N : ℕ) : l2 (psi N) ^ 2 = gaussMoment (2 * N) := by sorry
