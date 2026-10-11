-- Prove2me | Theorems.Thm_BookProof_YangMillsAbelianEsa_ymMomIdx_val
-- name    : BookProof.YangMillsAbelianEsa.ymMomIdx_val
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T18:19:52.46897+00:00
-- url     : https://prove2.me/theorems/b93059c5-ce46-46ed-8c31-e6174bc7b5f5
-- title:
--   `BookProof.YangMillsAbelianEsa.ymMomIdx_val` (m : Fin 24) : (ymMomIdx m).val = 3 + m.val
-- statement:
--   Prove the following Lean 4 theorem from `ChapterYangMillsAbelianEsa`.
--
--   `BookProof.YangMillsAbelianEsa.ymMomIdx_val` (m : Fin 24) : (ymMomIdx m).val = 3 + m.val
--
--   Formalization note: Lean 4 identifier `BookProof.YangMillsAbelianEsa.ymMomIdx_val`.

-- Generated from ChapterYangMillsAbelianEsa.lean — theorem BookProof.YangMillsAbelianEsa.ymMomIdx_val
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
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

theorem BookProof.YangMillsAbelianEsa.ymMomIdx_val (m : Fin 24) : (ymMomIdx m).val = 3 + m.val := by sorry
