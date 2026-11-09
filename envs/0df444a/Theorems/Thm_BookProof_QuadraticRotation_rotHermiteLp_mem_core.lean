-- Prove2me | Theorems.Thm_BookProof_QuadraticRotation_rotHermiteLp_mem_core
-- name    : BookProof.QuadraticRotation.rotHermiteLp_mem_core
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T00:24:53.446438+00:00
-- url     : https://prove2.me/theorems/d9b17fce-b775-49ec-91f9-0fc104cbef05
-- title:
--   The Lean 4 theorem `rotHermiteLp_mem_core` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `rotHermiteLp_mem_core` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuadraticRotationEsa.lean

-- Generated from ChapterQuadraticRotationEsa.lean — theorem BookProof.QuadraticRotation.rotHermiteLp_mem_core
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
open BookProof.HermiteProductBasis
open BookProof.HermiteProductCore
open BookProof.QuadraticRotation



open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

theorem BookProof.QuadraticRotation.rotHermiteLp_mem_core (O : Matrix (Fin d) (Fin d) ℝ) (a : Fin d →₀ ℕ) :
    rotHermiteLp O a ∈ polyGaussCore (d := d) := by sorry
