-- Prove2me | Theorems.Thm_BookProof_QuadraticRotation_exists_rotConj_eigenvalues
-- name    : BookProof.QuadraticRotation.exists_rotConj_eigenvalues
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T23:23:36.369979+00:00
-- url     : https://prove2.me/theorems/d56dce1b-7e07-4baf-a493-25d5bced37ba
-- title:
--   The Lean 4 theorem `exists_rotConj_eigenvalues` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.QuadraticRotation.exists_rotConj_eigenvalues` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterQuadraticRotationEsa.lean — theorem BookProof.QuadraticRotation.exists_rotConj_eigenvalues
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

theorem BookProof.QuadraticRotation.exists_rotConj_eigenvalues {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) :
    ∃ O : Matrix (Fin d) (Fin d) ℝ, Oᵀ * O = 1 ∧ A = rotConj O hA.eigenvalues := by sorry
