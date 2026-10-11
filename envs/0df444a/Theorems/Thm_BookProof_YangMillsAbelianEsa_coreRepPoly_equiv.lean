-- Prove2me | Theorems.Thm_BookProof_YangMillsAbelianEsa_coreRepPoly_equiv
-- name    : BookProof.YangMillsAbelianEsa.coreRepPoly_equiv
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T18:21:17.659605+00:00
-- url     : https://prove2.me/theorems/b6ef028a-7707-460d-8084-db3939159d46
-- title:
--   `BookProof.YangMillsAbelianEsa.coreRepPoly_equiv` (p : MvPolynomial (Fin 99) ℂ) : (coreRepPoly 99).equiv p = coreEquiv p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterYangMillsAbelianEsa`.
--
--   `BookProof.YangMillsAbelianEsa.coreRepPoly_equiv` (p : MvPolynomial (Fin 99) ℂ) : (coreRepPoly 99).equiv p = coreEquiv p
--
--   Formalization note: Lean 4 identifier `BookProof.YangMillsAbelianEsa.coreRepPoly_equiv`.

-- Generated from ChapterYangMillsAbelianEsa.lean — theorem BookProof.YangMillsAbelianEsa.coreRepPoly_equiv
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterYangMillsAbelianEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterYangMillsHermite
open BookProof.HermiteProductCore
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData
open BookProof.YangMillsHermite
open BookProof.YangMillsAbelianEsa



open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.FullQuadratic
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.HashimotoShiftInvert BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs

noncomputable section

theorem BookProof.YangMillsAbelianEsa.coreRepPoly_equiv (p : MvPolynomial (Fin 99) ℂ) :
    (coreRepPoly 99).equiv p = coreEquiv p := by sorry
