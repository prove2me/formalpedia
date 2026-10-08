-- Prove2me | Theorems.Thm_BookProof_QuadraticRotation_orthonormal_rotHermiteLp
-- name    : BookProof.QuadraticRotation.orthonormal_rotHermiteLp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-04T14:08:48.763311+00:00
-- url     : https://prove2.me/theorems/14eaa42a-6a8c-4d36-8d8b-8822c8b8c646
-- title:
--   The Lean 4 theorem `orthonormal_rotHermiteLp` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.QuadraticRotation.orthonormal_rotHermiteLp` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterQuadraticRotationEsa.lean — theorem BookProof.QuadraticRotation.orthonormal_rotHermiteLp
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterA4
open BookProof.HermiteProductBasis
open BookProof.HermiteProductCore
open BookProof.QuadraticRotation

variable {d : ℕ}



open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

theorem BookProof.QuadraticRotation.orthonormal_rotHermiteLp {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) :
    Orthonormal ℂ (rotHermiteLp (d := d) O) := by sorry
