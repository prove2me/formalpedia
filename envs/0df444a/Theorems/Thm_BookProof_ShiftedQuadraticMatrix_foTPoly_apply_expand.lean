-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadraticMatrix_foTPoly_apply_expand
-- name    : BookProof.ShiftedQuadraticMatrix.foTPoly_apply_expand
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T23:00:00.271976+00:00
-- url     : https://prove2.me/theorems/615db814-5bfa-46c3-9762-64ae3cda353d
-- title:
--   `BookProof.ShiftedQuadraticMatrix.foTPoly_apply_expand` (a k : Vd d) (b b' : Fin d → ℝ) (f : MvPolynomial (Fin d) ℂ) : foTPoly a k b b' f = ∑ i, ((b i : ℝ) : ℂ) • (X i * f) + ∑ i,
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticMatrixEsa`.
--
--   `BookProof.ShiftedQuadraticMatrix.foTPoly_apply_expand` (a k : Vd d) (b b' : Fin d → ℝ) (f : MvPolynomial (Fin d) ℂ) : foTPoly a k b b' f = ∑ i, ((b i : ℝ) : ℂ) • (X i * f) + ∑ i, ((b' i : ℝ) : ℂ) • momPoly i f + ((∑ i, (b i * a i + b' i * k i) : ℝ) : ℂ) • f
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadraticMatrix.foTPoly_apply_expand`.

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — theorem BookProof.ShiftedQuadraticMatrix.foTPoly_apply_expand
import Definitions.Def_ChapterHermiteProductBasis
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
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.HermiteProductCore
open BookProof.NavierStokesFlow.DifferentialL2
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

theorem BookProof.ShiftedQuadraticMatrix.foTPoly_apply_expand (a k : Vd d) (b b' : Fin d → ℝ) (f : MvPolynomial (Fin d) ℂ) :
    foTPoly a k b b' f
      = ∑ i, ((b i : ℝ) : ℂ) • (X i * f) + ∑ i, ((b' i : ℝ) : ℂ) • momPoly i f
        + ((∑ i, (b i * a i + b' i * k i) : ℝ) : ℂ) • f := by sorry
