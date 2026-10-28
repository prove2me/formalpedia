-- Prove2me | Theorems.Thm_BookProof_QuadraticRotation_exists_rotConj
-- name    : BookProof.QuadraticRotation.exists_rotConj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-25T03:23:12.143247+00:00
-- url     : https://prove2.me/theorems/88ce6a9a-53c1-449e-bdf7-3876da254d68
-- title:
--   The Lean 4 theorem `exists_rotConj` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `exists_rotConj` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuadraticRotationEsa.lean

-- Generated from ChapterQuadraticRotationEsa.lean — theorem BookProof.QuadraticRotation.exists_rotConj
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
open BookProof.QuadraticRotation



open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

theorem BookProof.QuadraticRotation.exists_rotConj {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) :
    ∃ (O : Matrix (Fin d) (Fin d) ℝ) (c : Fin d → ℝ), Oᵀ * O = 1 ∧ A = rotConj O c := by sorry
