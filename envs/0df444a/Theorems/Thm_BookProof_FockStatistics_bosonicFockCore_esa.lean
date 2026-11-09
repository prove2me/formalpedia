-- Prove2me | Theorems.Thm_BookProof_FockStatistics_bosonicFockCore_esa
-- name    : BookProof.FockStatistics.bosonicFockCore_esa
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T20:30:49.225618+00:00
-- url     : https://prove2.me/theorems/7bad4c54-0f24-4e9b-9994-6d12e97da4a5
-- title:
--   `BookProof.FockStatistics.bosonicFockCore_esa` (hcore : IsGraphCore D₀ A) : EssentiallySelfAdjointOn (bosonicFockCoreDom Hs D D₀) (bosonicFockCoreOp Hs D A D₀)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockStatisticsEsa`.
--
--   `BookProof.FockStatistics.bosonicFockCore_esa` (hcore : IsGraphCore D₀ A) : EssentiallySelfAdjointOn (bosonicFockCoreDom Hs D D₀) (bosonicFockCoreOp Hs D A D₀)
--
--   Formalization note: Lean 4 identifier `BookProof.FockStatistics.bosonicFockCore_esa`.

-- Generated from ChapterFockStatisticsEsa.lean — theorem BookProof.FockStatistics.bosonicFockCore_esa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Definitions.Def_ChapterEsaOneParticleDGamma
import Mathlib
import Definitions.Def_ChapterFockStatisticsEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterFockStatisticsCompletion
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterScalarDGammaEsa
open BookProof.DirectSumEsa
open BookProof.GraphCore
open BookProof.TensorCore



open scoped TensorProduct ENNReal
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.TensorPerm BookProof.PermSector
open BookProof.SecondQuantizationCore BookProof.DirectSumEsa

noncomputable section

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]
variable {Hs : IPSpace} [CompleteSpace Hs.carrier] {D : Submodule ℂ Hs.carrier}
  (A : D →ₗ[ℂ] Hs.carrier) (hdense : Dense (D : Set Hs.carrier)) (hsym : SymmetricOn D A)
  (hesa : EssentiallySelfAdjointOn D A)
variable (Hs : IPSpace) (D : Submodule ℂ Hs.carrier) (A : D →ₗ[ℂ] Hs.carrier)
variable (D₀ : Submodule ℂ Hs.carrier)
variable {D₀ : Submodule ℂ Hs.carrier}
  (D₀ : Submodule ℂ Hs.carrier)

include hdense hesa hsym in

theorem BookProof.FockStatistics.bosonicFockCore_esa (hcore : IsGraphCore D₀ A) :
    EssentiallySelfAdjointOn (bosonicFockCoreDom Hs D D₀) (bosonicFockCoreOp Hs D A D₀) := by sorry
