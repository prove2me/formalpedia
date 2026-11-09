-- Prove2me | Theorems.Thm_BookProof_NsLagrangianOuterFock_lagOne_dGamma_symmetricOn
-- name    : BookProof.NsLagrangianOuterFock.lagOne_dGamma_symmetricOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T21:31:01.674534+00:00
-- url     : https://prove2.me/theorems/eb6e6404-e54a-4e74-9be1-c42db55b103c
-- title:
--   `BookProof.NsLagrangianOuterFock.lagOne_dGamma_symmetricOn` (nu : ℝ) (hnu : 0 < nu) (f : Fin 3 → ℝ) : SymmetricOn (dsCore (fun n : ℕ => fockSectorCore lagOneSpace (lpFiniteModes Ve
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsLagrangianOuterFockEsa`.
--
--   `BookProof.NsLagrangianOuterFock.lagOne_dGamma_symmetricOn` (nu : ℝ) (hnu : 0 < nu) (f : Fin 3 → ℝ) : SymmetricOn (dsCore (fun n : ℕ => fockSectorCore lagOneSpace (lpFiniteModes Vel) (lpFiniteModes Vel) n)) (dGammaCoreOp lagOneSpace (lpFiniteModes Vel) (lagOneOp nu hnu f) (lpFiniteModes Vel))
--
--   Formalization note: Lean 4 identifier `BookProof.NsLagrangianOuterFock.lagOne_dGamma_symmetricOn`.

-- Generated from ChapterNsLagrangianOuterFockEsa.lean — theorem BookProof.NsLagrangianOuterFock.lagOne_dGamma_symmetricOn
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterFockStatisticsCompletion
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterReducingSubspaceEsa
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
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterNavierStokesLagrangianCanonical
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterScalarDGammaEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.DirectSumEsa
open BookProof.NavierStokesFlow.ThreeComponent



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
open BookProof.PermSector BookProof.ReducedEsa
open BookProof.DirectSumEsa BookProof.SecondQuantizationCore
open BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LagrangianCanonical
open BookProof.NavierStokesFlow.LagrangianKatoRellich
open BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.IkebeKato

noncomputable section

theorem BookProof.NsLagrangianOuterFock.lagOne_dGamma_symmetricOn (nu : ℝ) (hnu : 0 < nu) (f : Fin 3 → ℝ) :
    SymmetricOn
      (dsCore (fun n : ℕ => fockSectorCore lagOneSpace (lpFiniteModes Vel)
        (lpFiniteModes Vel) n))
      (dGammaCoreOp lagOneSpace (lpFiniteModes Vel) (lagOneOp nu hnu f)
        (lpFiniteModes Vel)) := by sorry
