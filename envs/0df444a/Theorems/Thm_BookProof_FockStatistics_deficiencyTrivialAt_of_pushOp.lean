-- Prove2me | Theorems.Thm_BookProof_FockStatistics_deficiencyTrivialAt_of_pushOp
-- name    : BookProof.FockStatistics.deficiencyTrivialAt_of_pushOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T20:29:51.443938+00:00
-- url     : https://prove2.me/theorems/af457aec-26b7-4b9d-b9b0-1db0ec21b91d
-- title:
--   `BookProof.FockStatistics.deficiencyTrivialAt_of_pushOp` (U : F →ₗᵢ[ℂ] G) {D : Submodule ℂ F} (T : D →ₗ[ℂ] F) {z : ℂ} (h : DeficiencyTrivialAt (pushDom U D) (pushOp U T) z) : Defic
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockStatisticsEsa`.
--
--   `BookProof.FockStatistics.deficiencyTrivialAt_of_pushOp` (U : F →ₗᵢ[ℂ] G) {D : Submodule ℂ F} (T : D →ₗ[ℂ] F) {z : ℂ} (h : DeficiencyTrivialAt (pushDom U D) (pushOp U T) z) : DeficiencyTrivialAt D T z
--
--   Formalization note: Lean 4 identifier `BookProof.FockStatistics.deficiencyTrivialAt_of_pushOp`.

-- Generated from ChapterFockStatisticsEsa.lean — theorem BookProof.FockStatistics.deficiencyTrivialAt_of_pushOp
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

theorem BookProof.FockStatistics.deficiencyTrivialAt_of_pushOp (U : F →ₗᵢ[ℂ] G) {D : Submodule ℂ F} (T : D →ₗ[ℂ] F)
    {z : ℂ} (h : DeficiencyTrivialAt (pushDom U D) (pushOp U T) z) :
    DeficiencyTrivialAt D T z := by sorry
