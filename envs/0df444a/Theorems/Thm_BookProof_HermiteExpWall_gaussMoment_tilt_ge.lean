-- Prove2me | Theorems.Thm_BookProof_HermiteExpWall_gaussMoment_tilt_ge
-- name    : BookProof.HermiteExpWall.gaussMoment_tilt_ge
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:09:39.740011+00:00
-- url     : https://prove2.me/theorems/81f9f2df-0303-49ce-b423-5bda8e852b59
-- title:
--   `BookProof.HermiteExpWall.gaussMoment_tilt_ge` (s : ℝ) (N : ℕ) : (s ^ 8 / 315) * gaussMoment (2 * N + 8) ≤ ∫ x : ℝ, Real.exp (-(2 * s) * x) * (x ^ (2 * N) * gaussW x)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteExpWall`.
--
--   `BookProof.HermiteExpWall.gaussMoment_tilt_ge` (s : ℝ) (N : ℕ) : (s ^ 8 / 315) * gaussMoment (2 * N + 8) ≤ ∫ x : ℝ, Real.exp (-(2 * s) * x) * (x ^ (2 * N) * gaussW x)
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteExpWall.gaussMoment_tilt_ge`.

-- Generated from ChapterHermiteExpWall.lean — theorem BookProof.HermiteExpWall.gaussMoment_tilt_ge
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

theorem BookProof.HermiteExpWall.gaussMoment_tilt_ge (s : ℝ) (N : ℕ) :
    (s ^ 8 / 315) * gaussMoment (2 * N + 8)
      ≤ ∫ x : ℝ, Real.exp (-(2 * s) * x) * (x ^ (2 * N) * gaussW x) := by sorry
