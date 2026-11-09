-- Prove2me | Theorems.Thm_BookProof_ModeQuadratic_sub_single_one_one
-- name    : BookProof.ModeQuadratic.sub_single_one_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T12:33:29.332305+00:00
-- url     : https://prove2.me/theorems/c518a318-6ff5-40d2-9a85-fa232d7ca15d
-- title:
--   `BookProof.ModeQuadratic.sub_single_one_one` (i : Fin d) (a : Fin d →₀ ℕ) : a - Finsupp.single i 1 - Finsupp.single i 1 = a - Finsupp.single i 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterModeQuadraticEsa`.
--
--   `BookProof.ModeQuadratic.sub_single_one_one` (i : Fin d) (a : Fin d →₀ ℕ) : a - Finsupp.single i 1 - Finsupp.single i 1 = a - Finsupp.single i 2
--
--   Formalization note: Lean 4 identifier `BookProof.ModeQuadratic.sub_single_one_one`.

-- Generated from ChapterModeQuadraticEsa.lean — theorem BookProof.ModeQuadratic.sub_single_one_one
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterModeQuadraticEsaPromoted
import Definitions.Def_ChapterGaussCoreQuadBounds
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

theorem BookProof.ModeQuadratic.sub_single_one_one (i : Fin d) (a : Fin d →₀ ℕ) :
    a - Finsupp.single i 1 - Finsupp.single i 1 = a - Finsupp.single i 2 := by sorry
