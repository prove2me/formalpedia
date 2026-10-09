-- Prove2me | Theorems.Thm_BookProof_HermiteExpWall_integral_gaussPoly_sq
-- name    : BookProof.HermiteExpWall.integral_gaussPoly_sq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:11:14.2853+00:00
-- url     : https://prove2.me/theorems/bdf0881e-bc0c-4208-9fce-d31fd9185858
-- title:
--   `BookProof.HermiteExpWall.integral_gaussPoly_sq` (q : Polynomial ℝ) : ∫ x : ℝ, gaussPoly q x ^ 2 = gint (q * q)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteExpWall`.
--
--   `BookProof.HermiteExpWall.integral_gaussPoly_sq` (q : Polynomial ℝ) : ∫ x : ℝ, gaussPoly q x ^ 2 = gint (q * q)
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteExpWall.integral_gaussPoly_sq`.

-- Generated from ChapterHermiteExpWall.lean — theorem BookProof.HermiteExpWall.integral_gaussPoly_sq
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterHermiteProductCore
import Mathlib
import Definitions.Def_ChapterHermiteExpWall
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterQgHermiteCore
open BookProof.HermiteCore
open BookProof.QgHermiteCore
open BookProof.HermiteExpWall



open MeasureTheory Polynomial
open BookProof.HermiteCore BookProof.Starobinsky BookProof.QgHermiteCore
open BookProof.HermiteProductCore

noncomputable section

theorem BookProof.HermiteExpWall.integral_gaussPoly_sq (q : Polynomial ℝ) :
    ∫ x : ℝ, gaussPoly q x ^ 2 = gint (q * q) := by sorry
