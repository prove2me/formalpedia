-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadratic_shiftedHPoly_term
-- name    : BookProof.ShiftedQuadratic.shiftedHPoly_term
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T12:25:49.037729+00:00
-- url     : https://prove2.me/theorems/5f754a35-fd70-440c-ba70-6318a3667906
-- title:
--   `BookProof.ShiftedQuadratic.shiftedHPoly_term` (c b b' : Fin d → ℝ) (i : Fin d) (hc : c i ≠ 0) (p : MvPolynomial (Fin d) ℂ) : ((c i : ℝ) : ℂ) • oscTPoly (shiftVec c b) (boostVec c
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticEsa`.
--
--   `BookProof.ShiftedQuadratic.shiftedHPoly_term` (c b b' : Fin d → ℝ) (i : Fin d) (hc : c i ≠ 0) (p : MvPolynomial (Fin d) ℂ) : ((c i : ℝ) : ℂ) • oscTPoly (shiftVec c b) (boostVec c b') i p + ((b i : ℝ) : ℂ) • mulXTPoly (shiftVec c b) i p + ((b' i : ℝ) : ℂ) • momTPoly (boostVec c b') i p = ((c i : ℝ) : ℂ) • oscPoly i p + (((-(b' i ^ 2) / (4 * c i) - b i ^ 2 / c i : ℝ)) : ℂ) • p
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadratic.shiftedHPoly_term`.

-- Generated from ChapterShiftedQuadraticEsa.lean — theorem BookProof.ShiftedQuadratic.shiftedHPoly_term
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.HyperbolicQuadratic
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.ShiftedHermiteCore
open BookProof.ShiftedQuadratic



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
open BookProof.ShiftedHermiteCore
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.ShiftedQuadratic.shiftedHPoly_term (c b b' : Fin d → ℝ) (i : Fin d) (hc : c i ≠ 0)
    (p : MvPolynomial (Fin d) ℂ) :
    ((c i : ℝ) : ℂ) • oscTPoly (shiftVec c b) (boostVec c b') i p
        + ((b i : ℝ) : ℂ) • mulXTPoly (shiftVec c b) i p
        + ((b' i : ℝ) : ℂ) • momTPoly (boostVec c b') i p
      = ((c i : ℝ) : ℂ) • oscPoly i p
        + (((-(b' i ^ 2) / (4 * c i) - b i ^ 2 / c i : ℝ)) : ℂ) • p := by sorry
