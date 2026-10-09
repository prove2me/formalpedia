-- Prove2me | Theorems.Thm_BookProof_QuadraticRotation_rotConj_eq
-- name    : BookProof.QuadraticRotation.rotConj_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T23:23:37.257984+00:00
-- url     : https://prove2.me/theorems/d5ad5baa-e338-4e83-812a-89bd3185cd7e
-- title:
--   The Lean 4 theorem `rotConj_eq` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.QuadraticRotation.rotConj_eq` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterQuadraticRotationEsa.lean — theorem BookProof.QuadraticRotation.rotConj_eq
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
open BookProof.QuadraticRotation



open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

theorem BookProof.QuadraticRotation.rotConj_eq (O : Matrix (Fin d) (Fin d) ℝ) (c : Fin d → ℝ) :
    rotConj O c = O * Matrix.diagonal c * Oᵀ := by sorry
