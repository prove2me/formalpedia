-- Prove2me | Theorems.Thm_BookProof_FockStatistics_fermionicFockOp_single
-- name    : BookProof.FockStatistics.fermionicFockOp_single
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-10T14:32:14.888495+00:00
-- url     : https://prove2.me/theorems/34685ee7-cf9e-4d6e-abd8-3f042eb8c89c
-- title:
--   `BookProof.FockStatistics.fermionicFockOp_single` (n : ℕ) (u : redDom (fermionicProj Hs n) (sectorDom Hs D n)) : (fermionicFockOp Hs D A ⟨lp.single 2 n ((u : sector (fermionicProj
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockStatisticsEsa`.
--
--   `BookProof.FockStatistics.fermionicFockOp_single` (n : ℕ) (u : redDom (fermionicProj Hs n) (sectorDom Hs D n)) : (fermionicFockOp Hs D A ⟨lp.single 2 n ((u : sector (fermionicProj Hs n))), single_mem_dsCore (D := fun n : ℕ => redDom (fermionicProj Hs n) (sectorDom Hs D n)) n u⟩ : fermionicFock Hs) = lp.single 2 n (fermionicSectorOp Hs D A n u)
--
--   Formalization note: Lean 4 identifier `BookProof.FockStatistics.fermionicFockOp_single`.

-- Generated from ChapterFockStatisticsEsa.lean — theorem BookProof.FockStatistics.fermionicFockOp_single
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
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterFockStatisticsCompletion
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterScalarDGammaEsa
import Theorems.Thm_BookProof_DirectSumEsa_single_mem_dsCore
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

theorem BookProof.FockStatistics.fermionicFockOp_single (n : ℕ)
    (u : redDom (fermionicProj Hs n) (sectorDom Hs D n)) :
    (fermionicFockOp Hs D A ⟨lp.single 2 n ((u : sector (fermionicProj Hs n))),
        single_mem_dsCore (D := fun n : ℕ => redDom (fermionicProj Hs n) (sectorDom Hs D n))
          n u⟩ : fermionicFock Hs)
      = lp.single 2 n (fermionicSectorOp Hs D A n u) := by sorry
