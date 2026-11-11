-- Prove2me | Theorems.Thm_BookProof_FockStatistics_fermionicFock_symmetricOn_inc
-- name    : BookProof.FockStatistics.fermionicFock_symmetricOn_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-10T06:54:57.293836+00:00
-- url     : https://prove2.me/theorems/44834cb6-b82c-41b8-abc1-8580a3679ea2
-- title:
--   `BookProof.FockStatistics.fermionicFock_symmetricOn_inc` : SymmetricOn (fermionicFockDom Hs D) (fermionicFockOp Hs D A)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockStatisticsEsa`.
--
--   `BookProof.FockStatistics.fermionicFock_symmetricOn_inc` : SymmetricOn (fermionicFockDom Hs D) (fermionicFockOp Hs D A)
--
--   Formalization note: Lean 4 identifier `BookProof.FockStatistics.fermionicFock_symmetricOn_inc`.
--
--   Replaces the published node `BookProof_FockStatistics_fermionicFock_symmetricOn`, whose preamble declared the section `variable` block twice: Lean read the second `(Hs) (D) (A)` as new variables, so its target carried the hypotheses on one `(D, A)` and the conclusion on another and no proof could exist.  The `_inc` twin is the same statement with the re-declarations removed.

-- Generated from ChapterFockStatisticsEsa.lean — theorem BookProof.FockStatistics.fermionicFock_symmetricOn_inc
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
variable (D₀ : Submodule ℂ Hs.carrier)

include hsym in

theorem BookProof.FockStatistics.fermionicFock_symmetricOn_inc :
    SymmetricOn (fermionicFockDom Hs D) (fermionicFockOp Hs D A) := by sorry
