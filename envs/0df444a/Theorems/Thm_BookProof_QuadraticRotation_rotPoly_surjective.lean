-- Prove2me | Theorems.Thm_BookProof_QuadraticRotation_rotPoly_surjective
-- name    : BookProof.QuadraticRotation.rotPoly_surjective
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T23:22:14.987645+00:00
-- url     : https://prove2.me/theorems/d1f40291-9f29-4ebb-9ee9-229e2177d1f0
-- title:
--   The Lean 4 theorem `rotPoly_surjective` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.QuadraticRotation.rotPoly_surjective` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterQuadraticRotationEsa.lean — theorem BookProof.QuadraticRotation.rotPoly_surjective
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

theorem BookProof.QuadraticRotation.rotPoly_surjective {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) :
    Function.Surjective (rotPoly O) := by sorry
