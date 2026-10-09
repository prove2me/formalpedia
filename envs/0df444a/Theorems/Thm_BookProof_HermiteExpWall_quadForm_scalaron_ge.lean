-- Prove2me | Theorems.Thm_BookProof_HermiteExpWall_quadForm_scalaron_ge
-- name    : BookProof.HermiteExpWall.quadForm_scalaron_ge
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:11:21.013985+00:00
-- url     : https://prove2.me/theorems/174d0f80-b5ad-4ae5-8af7-063eff069288
-- title:
--   `BookProof.HermiteExpWall.quadForm_scalaron_ge` (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha) (N : ℕ) : (M ^ 4 / (16 * alpha)) * ((8 * (Real.sqrt (2 / 3) / M) ^ 8 / 315) * (N : ℝ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteExpWall`.
--
--   `BookProof.HermiteExpWall.quadForm_scalaron_ge` (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha) (N : ℕ) : (M ^ 4 / (16 * alpha)) * ((8 * (Real.sqrt (2 / 3) / M) ^ 8 / 315) * (N : ℝ) ^ 4 - 1) * gaussMoment (2 * N) ≤ ∫ x : ℝ, starobinskyV M alpha x * psi N x ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteExpWall.quadForm_scalaron_ge`.

-- Generated from ChapterHermiteExpWall.lean — theorem BookProof.HermiteExpWall.quadForm_scalaron_ge
import Definitions.Def_ChapterQgHermiteCore
import Mathlib
import Definitions.Def_ChapterHermiteExpWall
import Definitions.Def_ChapterGhostField
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterStarobinskyPotential
open BookProof.GhostField
open BookProof.HermiteCore
open BookProof.HermiteProductCore
open BookProof.Starobinsky
open BookProof.HermiteExpWall



open MeasureTheory Polynomial
open BookProof.HermiteCore BookProof.Starobinsky BookProof.QgHermiteCore
open BookProof.HermiteProductCore

noncomputable section

theorem BookProof.HermiteExpWall.quadForm_scalaron_ge (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha) (N : ℕ) :
    (M ^ 4 / (16 * alpha)) *
        ((8 * (Real.sqrt (2 / 3) / M) ^ 8 / 315) * (N : ℝ) ^ 4 - 1) * gaussMoment (2 * N)
      ≤ ∫ x : ℝ, starobinskyV M alpha x * psi N x ^ 2 := by sorry
