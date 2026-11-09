-- Prove2me | Theorems.Thm_BookProof_FockStatistics_essentiallySelfAdjointOn_of_pushOp
-- name    : BookProof.FockStatistics.essentiallySelfAdjointOn_of_pushOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T20:31:03.066099+00:00
-- url     : https://prove2.me/theorems/5312cf4e-8cbe-484f-8413-6b711cf7153a
-- title:
--   `BookProof.FockStatistics.essentiallySelfAdjointOn_of_pushOp` (U : F →ₗᵢ[ℂ] G) {D : Submodule ℂ F} (T : D →ₗ[ℂ] F) (h : EssentiallySelfAdjointOn (pushDom U D) (pushOp U T)) : Essen
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockStatisticsEsa`.
--
--   `BookProof.FockStatistics.essentiallySelfAdjointOn_of_pushOp` (U : F →ₗᵢ[ℂ] G) {D : Submodule ℂ F} (T : D →ₗ[ℂ] F) (h : EssentiallySelfAdjointOn (pushDom U D) (pushOp U T)) : EssentiallySelfAdjointOn D T
--
--   Formalization note: Lean 4 identifier `BookProof.FockStatistics.essentiallySelfAdjointOn_of_pushOp`.

-- Generated from ChapterFockStatisticsEsa.lean — theorem BookProof.FockStatistics.essentiallySelfAdjointOn_of_pushOp
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Definitions.Def_ChapterEsaOneParticleDGamma
import Definitions.Def_ChapterDirectSumEsa
import Mathlib
import Definitions.Def_ChapterFockStatisticsEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterFockStatisticsCompletion
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterScalarDGammaEsa
open BookProof.GraphCore



open scoped TensorProduct ENNReal
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.TensorPerm BookProof.PermSector
open BookProof.SecondQuantizationCore BookProof.DirectSumEsa

noncomputable section

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

theorem BookProof.FockStatistics.essentiallySelfAdjointOn_of_pushOp (U : F →ₗᵢ[ℂ] G) {D : Submodule ℂ F}
    (T : D →ₗ[ℂ] F) (h : EssentiallySelfAdjointOn (pushDom U D) (pushOp U T)) :
    EssentiallySelfAdjointOn D T := by sorry
