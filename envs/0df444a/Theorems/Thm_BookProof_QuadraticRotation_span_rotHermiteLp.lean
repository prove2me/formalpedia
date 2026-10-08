-- Prove2me | Theorems.Thm_BookProof_QuadraticRotation_span_rotHermiteLp
-- name    : BookProof.QuadraticRotation.span_rotHermiteLp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-04T14:10:00.437956+00:00
-- url     : https://prove2.me/theorems/d9bcb916-4c3c-4b56-97f3-3ea6f779b474
-- title:
--   The Lean 4 theorem `span_rotHermiteLp` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.QuadraticRotation.span_rotHermiteLp` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterQuadraticRotationEsa.lean — theorem BookProof.QuadraticRotation.span_rotHermiteLp
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

theorem BookProof.QuadraticRotation.span_rotHermiteLp {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) :
    Submodule.span ℂ (Set.range (rotHermiteLp (d := d) O)) = polyGaussCore (d := d) := by sorry
