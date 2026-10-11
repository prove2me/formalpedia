-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadratic_shiftedHPoly_apply
-- name    : BookProof.ShiftedQuadratic.shiftedHPoly_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:26:23.710914+00:00
-- url     : https://prove2.me/theorems/4cb89db4-9dee-4124-96b5-801217fa872d
-- title:
--   `BookProof.ShiftedQuadratic.shiftedHPoly_apply` (a k : Vd d) (c b b' : Fin d → ℝ) (p : MvPolynomial (Fin d) ℂ) : shiftedHPoly a k c b b' p = ∑ i, (((c i : ℝ) : ℂ) • oscTPoly a k i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticEsa`.
--
--   `BookProof.ShiftedQuadratic.shiftedHPoly_apply` (a k : Vd d) (c b b' : Fin d → ℝ) (p : MvPolynomial (Fin d) ℂ) : shiftedHPoly a k c b b' p = ∑ i, (((c i : ℝ) : ℂ) • oscTPoly a k i p + ((b i : ℝ) : ℂ) • mulXTPoly a i p + ((b' i : ℝ) : ℂ) • momTPoly k i p)
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadratic.shiftedHPoly_apply`.

-- Generated from ChapterShiftedQuadraticEsa.lean — theorem BookProof.ShiftedQuadratic.shiftedHPoly_apply
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.HermiteProductCore
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

theorem BookProof.ShiftedQuadratic.shiftedHPoly_apply (a k : Vd d) (c b b' : Fin d → ℝ) (p : MvPolynomial (Fin d) ℂ) :
    shiftedHPoly a k c b b' p
      = ∑ i, (((c i : ℝ) : ℂ) • oscTPoly a k i p + ((b i : ℝ) : ℂ) • mulXTPoly a i p
          + ((b' i : ℝ) : ℂ) • momTPoly k i p) := by sorry
