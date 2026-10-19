-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadratic_oscTPoly_apply
-- name    : BookProof.ShiftedQuadratic.oscTPoly_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T22:59:41.161374+00:00
-- url     : https://prove2.me/theorems/130eabee-9b49-4b8a-ace1-7d3a705b4605
-- title:
--   `BookProof.ShiftedQuadratic.oscTPoly_apply` (a k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) : oscTPoly a k i p = oscPoly i p + (2 * ((k i : ℝ) : ℂ)) • momPoly i p + (((a i :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticEsa`.
--
--   `BookProof.ShiftedQuadratic.oscTPoly_apply` (a k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) : oscTPoly a k i p = oscPoly i p + (2 * ((k i : ℝ) : ℂ)) • momPoly i p + (((a i : ℝ) : ℂ) / 2) • (X i * p) + ((((k i : ℝ) : ℂ)) ^ 2 + ((a i : ℝ) : ℂ) ^ 2 / 4) • p
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadratic.oscTPoly_apply`.

-- Generated from ChapterShiftedQuadraticEsa.lean — theorem BookProof.ShiftedQuadratic.oscTPoly_apply
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.HermiteProductCore
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

theorem BookProof.ShiftedQuadratic.oscTPoly_apply (a k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    oscTPoly a k i p = oscPoly i p + (2 * ((k i : ℝ) : ℂ)) • momPoly i p
      + (((a i : ℝ) : ℂ) / 2) • (X i * p)
      + ((((k i : ℝ) : ℂ)) ^ 2 + ((a i : ℝ) : ℂ) ^ 2 / 4) • p := by sorry
