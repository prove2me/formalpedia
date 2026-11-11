-- Prove2me | Theorems.Thm_BookProof_FockStatistics_fermionicFockCore_esa_inc
-- name    : BookProof.FockStatistics.fermionicFockCore_esa_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-10T06:53:52.704197+00:00
-- url     : https://prove2.me/theorems/7e0e4b7a-204d-4581-93a7-b51f746b5ddd
-- title:
--   `BookProof.FockStatistics.fermionicFockCore_esa_inc` (hcore : IsGraphCore D₀ A) : EssentiallySelfAdjointOn (fermionicFockCoreDom Hs D D₀) (fermionicFockCoreOp Hs D A D₀)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockStatisticsEsa`.
--
--   `BookProof.FockStatistics.fermionicFockCore_esa_inc` (hcore : IsGraphCore D₀ A) : EssentiallySelfAdjointOn (fermionicFockCoreDom Hs D D₀) (fermionicFockCoreOp Hs D A D₀)
--
--   Formalization note: Lean 4 identifier `BookProof.FockStatistics.fermionicFockCore_esa_inc`.
--
--   Replaces the published node `BookProof_FockStatistics_fermionicFockCore_esa`, whose preamble declared the section `variable` block twice: Lean read the second `(Hs) (D) (A)` as new variables, so its target carried the hypotheses on one `(D, A)` and the conclusion on another and no proof could exist.  The `_inc` twin is the same statement with the re-declarations removed.

-- Generated from ChapterFockStatisticsEsa.lean — theorem BookProof.FockStatistics.fermionicFockCore_esa_inc
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
variable (D₀ : Submodule ℂ Hs.carrier)

include hdense hesa hsym in

theorem BookProof.FockStatistics.fermionicFockCore_esa_inc (hcore : IsGraphCore D₀ A) :
    EssentiallySelfAdjointOn (fermionicFockCoreDom Hs D D₀) (fermionicFockCoreOp Hs D A D₀) := by sorry
