-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadraticMatrix_shiftedHMatPoly_eq_quadPolyMat
-- name    : BookProof.ShiftedQuadraticMatrix.shiftedHMatPoly_eq_quadPolyMat
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T12:45:34.946982+00:00
-- url     : https://prove2.me/theorems/05c4025c-2e9d-4bbf-978f-9c67b9bda402
-- title:
--   `BookProof.ShiftedQuadraticMatrix.shiftedHMatPoly_eq_quadPolyMat` (a k : Vd d) {A : Matrix (Fin d) (Fin d) ℝ} (hsym : ∀ i j, A i j = A j i) (b b' : Fin d → ℝ) (ha : ∀ i, ∑ j, A i j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticMatrixEsa`.
--
--   `BookProof.ShiftedQuadraticMatrix.shiftedHMatPoly_eq_quadPolyMat` (a k : Vd d) {A : Matrix (Fin d) (Fin d) ℝ} (hsym : ∀ i j, A i j = A j i) (b b' : Fin d → ℝ) (ha : ∀ i, ∑ j, A i j * a j = -2 * b i) (hk : ∀ i, ∑ j, A i j * k j = -(b' i) / 2) (f : MvPolynomial (Fin d) ℂ) : shiftedHMatPoly a k A b b' f = quadPolyMat A f + ((matShiftConst a k b b' : ℝ) : ℂ) • f
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadraticMatrix.shiftedHMatPoly_eq_quadPolyMat`.

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — theorem BookProof.ShiftedQuadraticMatrix.shiftedHMatPoly_eq_quadPolyMat
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
open BookProof.HermiteProductCore
open BookProof.NavierStokesFlow.DifferentialL2
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

theorem BookProof.ShiftedQuadraticMatrix.shiftedHMatPoly_eq_quadPolyMat (a k : Vd d) {A : Matrix (Fin d) (Fin d) ℝ}
    (hsym : ∀ i j, A i j = A j i) (b b' : Fin d → ℝ)
    (ha : ∀ i, ∑ j, A i j * a j = -2 * b i)
    (hk : ∀ i, ∑ j, A i j * k j = -(b' i) / 2)
    (f : MvPolynomial (Fin d) ℂ) :
    shiftedHMatPoly a k A b b' f
      = quadPolyMat A f + ((matShiftConst a k b b' : ℝ) : ℂ) • f := by sorry
