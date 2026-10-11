-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadraticMatrix_quadTermT_apply
-- name    : BookProof.ShiftedQuadraticMatrix.quadTermT_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T22:59:57.534111+00:00
-- url     : https://prove2.me/theorems/56be4d59-ef52-42c2-a13d-de1f0b003e79
-- title:
--   `BookProof.ShiftedQuadraticMatrix.quadTermT_apply` (a k : Vd d) (A : Matrix (Fin d) (Fin d) ℝ) (p q : Fin d) (f : MvPolynomial (Fin d) ℂ) : ((A p q : ℝ) : ℂ) • ((momTPoly k p).comp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticMatrixEsa`.
--
--   `BookProof.ShiftedQuadraticMatrix.quadTermT_apply` (a k : Vd d) (A : Matrix (Fin d) (Fin d) ℝ) (p q : Fin d) (f : MvPolynomial (Fin d) ℂ) : ((A p q : ℝ) : ℂ) • ((momTPoly k p).comp (momTPoly k q) f + (1/4 : ℂ) • ((mulXTPoly a p).comp (mulXTPoly a q) f)) = ((A p q : ℝ) : ℂ) • (momPoly p (momPoly q f) + (1/4 : ℂ) • (X p * (X q * f))) + ((A p q * k q : ℝ) : ℂ) • momPoly p f + ((A p q * k p : ℝ) : ℂ) • momPoly q f + ((A p q * a q / 4 : ℝ) : ℂ) • (X p * f) + ((A p q * a p / 4 : ℝ) : ℂ) • (X q * f) + ((A p q * (k p * k q + a p * a q / 4) : ℝ) : ℂ) • f
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadraticMatrix.quadTermT_apply`.

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — theorem BookProof.ShiftedQuadraticMatrix.quadTermT_apply
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

theorem BookProof.ShiftedQuadraticMatrix.quadTermT_apply (a k : Vd d) (A : Matrix (Fin d) (Fin d) ℝ) (p q : Fin d)
    (f : MvPolynomial (Fin d) ℂ) :
    ((A p q : ℝ) : ℂ) • ((momTPoly k p).comp (momTPoly k q) f
        + (1/4 : ℂ) • ((mulXTPoly a p).comp (mulXTPoly a q) f))
      = ((A p q : ℝ) : ℂ) • (momPoly p (momPoly q f) + (1/4 : ℂ) • (X p * (X q * f)))
        + ((A p q * k q : ℝ) : ℂ) • momPoly p f + ((A p q * k p : ℝ) : ℂ) • momPoly q f
        + ((A p q * a q / 4 : ℝ) : ℂ) • (X p * f) + ((A p q * a p / 4 : ℝ) : ℂ) • (X q * f)
        + ((A p q * (k p * k q + a p * a q / 4) : ℝ) : ℂ) • f := by sorry
