-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadraticMatrix_hermiteTRLp_total
-- name    : BookProof.ShiftedQuadraticMatrix.hermiteTRLp_total
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:46:45.216772+00:00
-- url     : https://prove2.me/theorems/ef4c972a-b48a-4cd7-9b3f-2e80e8d3d031
-- title:
--   `BookProof.ShiftedQuadraticMatrix.hermiteTRLp_total` {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (a k : Vd d) (v : L2d d) (h : ∀ α, (inner ℂ (hermiteTRLp (d := d) O a k α) v :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticMatrixEsa`.
--
--   `BookProof.ShiftedQuadraticMatrix.hermiteTRLp_total` {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (a k : Vd d) (v : L2d d) (h : ∀ α, (inner ℂ (hermiteTRLp (d := d) O a k α) v : ℂ) = 0) : v = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadraticMatrix.hermiteTRLp_total`.

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — theorem BookProof.ShiftedQuadraticMatrix.hermiteTRLp_total
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.HermiteProductCore
open BookProof.ShiftedHermiteCore
open BookProof.ShiftedQuadraticMatrix



open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
open BookProof.QuadraticRotation
open BookProof.ShiftedHermiteCore
open BookProof.ShiftedQuadratic
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.ShiftedQuadraticMatrix.hermiteTRLp_total {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (a k : Vd d)
    (v : L2d d) (h : ∀ α, (inner ℂ (hermiteTRLp (d := d) O a k α) v : ℂ) = 0) : v = 0 := by sorry
