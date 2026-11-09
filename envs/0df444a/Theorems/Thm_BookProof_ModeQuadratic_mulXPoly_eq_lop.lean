-- Prove2me | Theorems.Thm_BookProof_ModeQuadratic_mulXPoly_eq_lop
-- name    : BookProof.ModeQuadratic.mulXPoly_eq_lop
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T12:33:56.995811+00:00
-- url     : https://prove2.me/theorems/5e987c7a-cadd-419b-9c81-a10262a06bab
-- title:
--   `BookProof.ModeQuadratic.mulXPoly_eq_lop` (i : Fin d) : mulXPoly (d := d) i = lop 1 i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterModeQuadraticEsa`.
--
--   `BookProof.ModeQuadratic.mulXPoly_eq_lop` (i : Fin d) : mulXPoly (d := d) i = lop 1 i
--
--   Formalization note: Lean 4 identifier `BookProof.ModeQuadratic.mulXPoly_eq_lop`.

-- Generated from ChapterModeQuadraticEsa.lean — theorem BookProof.ModeQuadratic.mulXPoly_eq_lop
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

theorem BookProof.ModeQuadratic.mulXPoly_eq_lop (i : Fin d) : mulXPoly (d := d) i = lop 1 i := by sorry
