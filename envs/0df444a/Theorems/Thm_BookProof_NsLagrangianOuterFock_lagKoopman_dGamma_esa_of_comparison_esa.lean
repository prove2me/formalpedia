-- Prove2me | Theorems.Thm_BookProof_NsLagrangianOuterFock_lagKoopman_dGamma_esa_of_comparison_esa
-- name    : BookProof.NsLagrangianOuterFock.lagKoopman_dGamma_esa_of_comparison_esa
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T21:32:21.588444+00:00
-- url     : https://prove2.me/theorems/dfbdc149-93fd-450b-83c3-3e2338a7e68b
-- title:
--   `BookProof.NsLagrangianOuterFock.lagKoopman_dGamma_esa_of_comparison_esa` (hN : EssentiallySelfAdjointOn (polyGaussCore (d := lagDim K)) (lagComparison S)) : EssentiallySelfAdjoint
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsLagrangianOuterFockEsa`.
--
--   `BookProof.NsLagrangianOuterFock.lagKoopman_dGamma_esa_of_comparison_esa` (hN : EssentiallySelfAdjointOn (polyGaussCore (d := lagDim K)) (lagComparison S)) : EssentiallySelfAdjointOn (dsCore (fun n : ℕ => fockSectorCore (L2dSpace (lagDim K)) (polyGaussCore (d := lagDim K)) (polyGaussCore (d := lagDim K)) n)) (dGammaCoreOp (L2dSpace (lagDim K)) (polyGaussCore (d := lagDim K)) (lagKoopmanOp S) (polyGaussCore (d := lagDim K)))
--
--   Formalization note: Lean 4 identifier `BookProof.NsLagrangianOuterFock.lagKoopman_dGamma_esa_of_comparison_esa`.

-- Generated from ChapterNsLagrangianOuterFockEsa.lean — theorem BookProof.NsLagrangianOuterFock.lagKoopman_dGamma_esa_of_comparison_esa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterFockStatisticsCompletion
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterYangMillsNonAbelianEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesLagrangianCanonical
import Definitions.Def_ChapterNavierStokesLagrangianKatoRellich
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesIkebeKato
import Mathlib
import Definitions.Def_ChapterNsLagrangianOuterFockEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterNavierStokesLagrangianCanonical
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterScalarDGammaEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterNsLagrangianDetFarisLavine
open BookProof.YangMillsNonAbelianEsa
open BookProof.DirectSumEsa
open BookProof.HermiteProductCore



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
open BookProof.PermSector BookProof.ReducedEsa
open BookProof.DirectSumEsa BookProof.SecondQuantizationCore
open BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LagrangianCanonical
open BookProof.NavierStokesFlow.LagrangianKatoRellich
open BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.IkebeKato
open BookProof.NsLagrangianDetFL

noncomputable section

variable {K : Type*} [Fintype K] (S : LagNsData K)

theorem BookProof.NsLagrangianOuterFock.lagKoopman_dGamma_esa_of_comparison_esa
    (hN : EssentiallySelfAdjointOn (polyGaussCore (d := lagDim K)) (lagComparison S)) :
    EssentiallySelfAdjointOn
      (dsCore (fun n : ℕ => fockSectorCore (L2dSpace (lagDim K))
        (polyGaussCore (d := lagDim K)) (polyGaussCore (d := lagDim K)) n))
      (dGammaCoreOp (L2dSpace (lagDim K)) (polyGaussCore (d := lagDim K))
        (lagKoopmanOp S) (polyGaussCore (d := lagDim K))) := by sorry
