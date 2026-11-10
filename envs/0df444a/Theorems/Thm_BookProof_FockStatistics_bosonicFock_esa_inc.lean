-- Prove2me | Theorems.Thm_BookProof_FockStatistics_bosonicFock_esa_inc
-- name    : BookProof.FockStatistics.bosonicFock_esa_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-10T03:25:01.341856+00:00
-- url     : https://prove2.me/theorems/489aabf9-c30c-4c27-9b71-84aa93a473be
-- title:
--   `BookProof.FockStatistics.bosonicFock_esa_inc` : EssentiallySelfAdjointOn (bosonicFockDom Hs D) (bosonicFockOp Hs D A)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockStatisticsEsa`.
--
--   `BookProof.FockStatistics.bosonicFock_esa_inc` : EssentiallySelfAdjointOn (bosonicFockDom Hs D) (bosonicFockOp Hs D A)
--
--   Formalization note: Lean 4 identifier `BookProof.FockStatistics.bosonicFock_esa_inc`.
--
--   Replaces the unprovable node `BookProof_FockStatistics_bosonicFock_esa`, whose stored preamble declared `Hs`, `D`, `A` (and `D₀`) a second time: Lean treats a re-declaration as a new variable, so the hypotheses constrain one `(D, A)` while the conclusion is about an unrelated one. The `_inc` suffix publishes the same statement with a single, correct variable block -- nothing else changes.

-- Generated from ChapterFockStatisticsEsa.lean — theorem BookProof.FockStatistics.bosonicFock_esa_inc
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

theorem BookProof.FockStatistics.bosonicFock_esa_inc :
    EssentiallySelfAdjointOn (bosonicFockDom Hs D) (bosonicFockOp Hs D A) := by sorry
