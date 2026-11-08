-- Prove2me | Theorems.Thm_BookProof_QuadraticRotation_rotHermiteLp_total
-- name    : BookProof.QuadraticRotation.rotHermiteLp_total
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T00:28:04.179538+00:00
-- url     : https://prove2.me/theorems/dbc02f2c-8fd9-4c57-8894-233ff889bdd9
-- title:
--   The Lean 4 theorem `rotHermiteLp_total` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `rotHermiteLp_total` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuadraticRotationEsa.lean

-- Generated from ChapterQuadraticRotationEsa.lean — theorem BookProof.QuadraticRotation.rotHermiteLp_total
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
open BookProof.HermiteProductCore
open BookProof.QuadraticRotation



open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

theorem BookProof.QuadraticRotation.rotHermiteLp_total {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (w : L2d d)
    (h : ∀ a, (inner ℂ (rotHermiteLp (d := d) O a) w : ℂ) = 0) : w = 0 := by sorry
