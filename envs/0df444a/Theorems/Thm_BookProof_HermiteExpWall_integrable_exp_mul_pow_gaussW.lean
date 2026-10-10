-- Prove2me | Theorems.Thm_BookProof_HermiteExpWall_integrable_exp_mul_pow_gaussW
-- name    : BookProof.HermiteExpWall.integrable_exp_mul_pow_gaussW
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:09:13.62984+00:00
-- url     : https://prove2.me/theorems/75df71e2-2290-4065-b5b1-de6b491f7b3a
-- title:
--   `BookProof.HermiteExpWall.integrable_exp_mul_pow_gaussW` (c : ℝ) (k : ℕ) : Integrable (fun x : ℝ => Real.exp (c * x) * (x ^ k * gaussW x))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteExpWall`.
--
--   `BookProof.HermiteExpWall.integrable_exp_mul_pow_gaussW` (c : ℝ) (k : ℕ) : Integrable (fun x : ℝ => Real.exp (c * x) * (x ^ k * gaussW x))
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteExpWall.integrable_exp_mul_pow_gaussW`.

-- Generated from ChapterHermiteExpWall.lean — theorem BookProof.HermiteExpWall.integrable_exp_mul_pow_gaussW
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterHermiteProductCore
import Mathlib
import Definitions.Def_ChapterHermiteExpWall
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteCore
open BookProof.HermiteExpWall



open MeasureTheory Polynomial
open BookProof.HermiteCore BookProof.Starobinsky BookProof.QgHermiteCore
open BookProof.HermiteProductCore

noncomputable section

theorem BookProof.HermiteExpWall.integrable_exp_mul_pow_gaussW (c : ℝ) (k : ℕ) :
    Integrable (fun x : ℝ => Real.exp (c * x) * (x ^ k * gaussW x)) := by sorry
