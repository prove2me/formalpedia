-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadratic_oscTPoly_eq
-- name    : BookProof.ShiftedQuadratic.oscTPoly_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:44:17.159388+00:00
-- url     : https://prove2.me/theorems/f9684a34-0fa0-4659-88f7-9915d4921a8c
-- title:
--   `BookProof.ShiftedQuadratic.oscTPoly_eq` (a k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) : oscTPoly a k i p = momTPoly k i (momTPoly k i p) + (1/4 : ℂ) • (mulXTPoly a i (mulX
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticEsa`.
--
--   `BookProof.ShiftedQuadratic.oscTPoly_eq` (a k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) : oscTPoly a k i p = momTPoly k i (momTPoly k i p) + (1/4 : ℂ) • (mulXTPoly a i (mulXTPoly a i p))
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadratic.oscTPoly_eq`.

-- Generated from ChapterShiftedQuadraticEsa.lean — theorem BookProof.ShiftedQuadratic.oscTPoly_eq
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

theorem BookProof.ShiftedQuadratic.oscTPoly_eq (a k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    oscTPoly a k i p
      = momTPoly k i (momTPoly k i p) + (1/4 : ℂ) • (mulXTPoly a i (mulXTPoly a i p)) := by sorry
