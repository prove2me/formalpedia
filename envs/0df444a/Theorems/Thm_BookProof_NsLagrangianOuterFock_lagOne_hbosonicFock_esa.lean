-- Prove2me | Theorems.Thm_BookProof_NsLagrangianOuterFock_lagOne_hbosonicFock_esa
-- name    : BookProof.NsLagrangianOuterFock.lagOne_hbosonicFock_esa
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T21:31:13.876368+00:00
-- url     : https://prove2.me/theorems/b2e8a964-9f12-4a3b-811a-3a10ca6f03a5
-- title:
--   `BookProof.NsLagrangianOuterFock.lagOne_hbosonicFock_esa` (nu : ℝ) (hnu : 0 < nu) (f : Fin 3 → ℝ) : EssentiallySelfAdjointOn (hbosonicFockDom lagOneSpace (lpFiniteModes Vel)) (hbos
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsLagrangianOuterFockEsa`.
--
--   `BookProof.NsLagrangianOuterFock.lagOne_hbosonicFock_esa` (nu : ℝ) (hnu : 0 < nu) (f : Fin 3 → ℝ) : EssentiallySelfAdjointOn (hbosonicFockDom lagOneSpace (lpFiniteModes Vel)) (hbosonicFockOp lagOneSpace (lpFiniteModes Vel) (lagOneOp nu hnu f))
--
--   Formalization note: Lean 4 identifier `BookProof.NsLagrangianOuterFock.lagOne_hbosonicFock_esa`.

-- Generated from ChapterNsLagrangianOuterFockEsa.lean — theorem BookProof.NsLagrangianOuterFock.lagOne_hbosonicFock_esa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterFockStatisticsCompletion
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsNonAbelianEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesLagrangianCanonical
import Definitions.Def_ChapterNavierStokesLagrangianKatoRellich
import Definitions.Def_ChapterNavierStokesIkebeKato
import Mathlib
import Definitions.Def_ChapterNsLagrangianOuterFockEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterNavierStokesLagrangianCanonical
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterScalarDGammaEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.FockStatistics
open BookProof.NavierStokesFlow.ThreeComponent
open BookProof.TensorCore



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
open BookProof.PermSector BookProof.ReducedEsa
open BookProof.DirectSumEsa BookProof.SecondQuantizationCore
open BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LagrangianCanonical
open BookProof.NavierStokesFlow.LagrangianKatoRellich
open BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.IkebeKato

noncomputable section

theorem BookProof.NsLagrangianOuterFock.lagOne_hbosonicFock_esa (nu : ℝ) (hnu : 0 < nu) (f : Fin 3 → ℝ) :
    EssentiallySelfAdjointOn (hbosonicFockDom lagOneSpace (lpFiniteModes Vel))
      (hbosonicFockOp lagOneSpace (lpFiniteModes Vel) (lagOneOp nu hnu f)) := by sorry
