-- Prove2me | Theorems.Thm_BookProof_ModeQuadratic_momPoly_eq_lop
-- name    : BookProof.ModeQuadratic.momPoly_eq_lop
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T12:34:28.934813+00:00
-- url     : https://prove2.me/theorems/a2f4139f-42d9-4c43-b577-cf17ca72ef95
-- title:
--   `BookProof.ModeQuadratic.momPoly_eq_lop` (i : Fin d) : momPoly (d := d) i = (Complex.I / 2) • lop (-1) i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterModeQuadraticEsa`.
--
--   `BookProof.ModeQuadratic.momPoly_eq_lop` (i : Fin d) : momPoly (d := d) i = (Complex.I / 2) • lop (-1) i
--
--   Formalization note: Lean 4 identifier `BookProof.ModeQuadratic.momPoly_eq_lop`.

-- Generated from ChapterModeQuadraticEsa.lean — theorem BookProof.ModeQuadratic.momPoly_eq_lop
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterModeQuadraticEsaPromoted
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.ModeQuadratic



open Finset MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.HyperbolicQuadratic
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.QuadratureEsa
open BookProof.CarlemanTwoStep
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.ModeQuadratic.momPoly_eq_lop (i : Fin d) :
    momPoly (d := d) i = (Complex.I / 2) • lop (-1) i := by sorry
