-- Prove2me | Theorems.Thm_BookProof_ModeQuadratic_sub_single_apply_self
-- name    : BookProof.ModeQuadratic.sub_single_apply_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T12:33:46.982802+00:00
-- url     : https://prove2.me/theorems/f73647ec-e830-4a7a-aa27-9fc6fb602864
-- title:
--   `BookProof.ModeQuadratic.sub_single_apply_self` (i : Fin d) (a : Fin d →₀ ℕ) : (a - Finsupp.single i 1 : Fin d →₀ ℕ) i = a i - 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterModeQuadraticEsa`.
--
--   `BookProof.ModeQuadratic.sub_single_apply_self` (i : Fin d) (a : Fin d →₀ ℕ) : (a - Finsupp.single i 1 : Fin d →₀ ℕ) i = a i - 1
--
--   Formalization note: Lean 4 identifier `BookProof.ModeQuadratic.sub_single_apply_self`.

-- Generated from ChapterModeQuadraticEsa.lean — theorem BookProof.ModeQuadratic.sub_single_apply_self
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

theorem BookProof.ModeQuadratic.sub_single_apply_self (i : Fin d) (a : Fin d →₀ ℕ) :
    (a - Finsupp.single i 1 : Fin d →₀ ℕ) i = a i - 1 := by sorry
