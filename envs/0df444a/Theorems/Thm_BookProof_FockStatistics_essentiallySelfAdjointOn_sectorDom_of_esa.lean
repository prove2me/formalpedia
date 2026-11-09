-- Prove2me | Theorems.Thm_BookProof_FockStatistics_essentiallySelfAdjointOn_sectorDom_of_esa
-- name    : BookProof.FockStatistics.essentiallySelfAdjointOn_sectorDom_of_esa
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T20:31:06.283723+00:00
-- url     : https://prove2.me/theorems/6b889a64-94d5-4998-a49b-35da0aa018f1
-- title:
--   `BookProof.FockStatistics.essentiallySelfAdjointOn_sectorDom_of_esa` (n : ℕ) : EssentiallySelfAdjointOn (sectorDom Hs D n) (sectorOp Hs D A n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockStatisticsEsa`.
--
--   `BookProof.FockStatistics.essentiallySelfAdjointOn_sectorDom_of_esa` (n : ℕ) : EssentiallySelfAdjointOn (sectorDom Hs D n) (sectorOp Hs D A n)
--
--   Formalization note: Lean 4 identifier `BookProof.FockStatistics.essentiallySelfAdjointOn_sectorDom_of_esa`.

-- Generated from ChapterFockStatisticsEsa.lean — theorem BookProof.FockStatistics.essentiallySelfAdjointOn_sectorDom_of_esa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Definitions.Def_ChapterEsaOneParticleDGamma
import Definitions.Def_ChapterDirectSumEsa
import Mathlib
import Definitions.Def_ChapterFockStatisticsEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterFockStatisticsCompletion
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterScalarDGammaEsa
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

include hdense hesa hsym in

theorem BookProof.FockStatistics.essentiallySelfAdjointOn_sectorDom_of_esa (n : ℕ) :
    EssentiallySelfAdjointOn (sectorDom Hs D n) (sectorOp Hs D A n) := by sorry
