-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadraticMatrix_span_hermiteTRLp
-- name    : BookProof.ShiftedQuadraticMatrix.span_hermiteTRLp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:46:44.157503+00:00
-- url     : https://prove2.me/theorems/f88584bd-7303-413b-ab73-43e8ba41633a
-- title:
--   `BookProof.ShiftedQuadraticMatrix.span_hermiteTRLp` {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (a k : Vd d) : Submodule.span ℂ (Set.range (hermiteTRLp (d := d) O a k)) = poly
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticMatrixEsa`.
--
--   `BookProof.ShiftedQuadraticMatrix.span_hermiteTRLp` {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (a k : Vd d) : Submodule.span ℂ (Set.range (hermiteTRLp (d := d) O a k)) = polyGaussCoreT a k
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadraticMatrix.span_hermiteTRLp`.

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — theorem BookProof.ShiftedQuadraticMatrix.span_hermiteTRLp
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
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.HermiteProductBasis
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

theorem BookProof.ShiftedQuadraticMatrix.span_hermiteTRLp {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (a k : Vd d) :
    Submodule.span ℂ (Set.range (hermiteTRLp (d := d) O a k)) = polyGaussCoreT a k := by sorry
