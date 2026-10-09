-- Prove2me | Theorems.Thm_BookProof_HermiteExpWall_gaussMoment_eq_integral
-- name    : BookProof.HermiteExpWall.gaussMoment_eq_integral
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:08:09.663247+00:00
-- url     : https://prove2.me/theorems/1cc813dd-2453-4518-b8e3-cb92f2a0be3b
-- title:
--   `BookProof.HermiteExpWall.gaussMoment_eq_integral` (k : ℕ) : gaussMoment k = ∫ x : ℝ, x ^ k * gaussW x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteExpWall`.
--
--   `BookProof.HermiteExpWall.gaussMoment_eq_integral` (k : ℕ) : gaussMoment k = ∫ x : ℝ, x ^ k * gaussW x
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteExpWall.gaussMoment_eq_integral`.

-- Generated from ChapterHermiteExpWall.lean — theorem BookProof.HermiteExpWall.gaussMoment_eq_integral
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQgHermiteCore
import Mathlib
import Definitions.Def_ChapterHermiteExpWall
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteCore
open BookProof.HermiteProductCore
open BookProof.HermiteExpWall



open MeasureTheory Polynomial
open BookProof.HermiteCore BookProof.Starobinsky BookProof.QgHermiteCore
open BookProof.HermiteProductCore

noncomputable section

theorem BookProof.HermiteExpWall.gaussMoment_eq_integral (k : ℕ) :
    gaussMoment k = ∫ x : ℝ, x ^ k * gaussW x := by sorry
