-- Prove2me | Theorems.Thm_BookProof_FockStatistics_fermionicFockCore_esa
-- name    : BookProof.FockStatistics.fermionicFockCore_esa
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T20:32:40.89524+00:00
-- url     : https://prove2.me/theorems/c932e962-219d-4dd5-87b0-0905d51321b0
-- title:
--   `BookProof.FockStatistics.fermionicFockCore_esa` (hcore : IsGraphCore D₀ A) : EssentiallySelfAdjointOn (fermionicFockCoreDom Hs D D₀) (fermionicFockCoreOp Hs D A D₀)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockStatisticsEsa`.
--
--   `BookProof.FockStatistics.fermionicFockCore_esa` (hcore : IsGraphCore D₀ A) : EssentiallySelfAdjointOn (fermionicFockCoreDom Hs D D₀) (fermionicFockCoreOp Hs D A D₀)
--
--   Formalization note: Lean 4 identifier `BookProof.FockStatistics.fermionicFockCore_esa`.

-- Generated from ChapterFockStatisticsEsa.lean — theorem BookProof.FockStatistics.fermionicFockCore_esa
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

theorem BookProof.FockStatistics.fermionicFockCore_esa (hcore : IsGraphCore D₀ A) :
    EssentiallySelfAdjointOn (fermionicFockCoreDom Hs D D₀) (fermionicFockCoreOp Hs D A D₀) := by sorry
