-- Prove2me | Theorems.Thm_BookProof_TwoParticleSector_symmetricOn_bosonic
-- name    : BookProof.TwoParticleSector.symmetricOn_bosonic
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-23T23:26:41.143461+00:00
-- url     : https://prove2.me/theorems/e214d91e-92c9-420b-9223-65874f5d6c51
-- title:
--   `BookProof.TwoParticleSector.symmetricOn_bosonic` (hA : SymmetricOn D₂ A) : SymmetricOn (redDom (bosonicProj Hs) (sectorDom Hs D₂ 2)) (redOp (sectorOp Hs D₂ A 2) (isReducingProject
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTwoParticleSectorEsa`.
--
--   `BookProof.TwoParticleSector.symmetricOn_bosonic` (hA : SymmetricOn D₂ A) : SymmetricOn (redDom (bosonicProj Hs) (sectorDom Hs D₂ 2)) (redOp (sectorOp Hs D₂ A 2) (isReducingProjection_bosonicProj Hs) (commutes_symProj (T := sectorOp Hs D₂ A 2) (hUD := fun _ hx => swapH_mem_sectorDom Hs D₂ hx) (sectorOp_swapH Hs D₂ A)))
--
--   Formalization note: Lean 4 identifier `BookProof.TwoParticleSector.symmetricOn_bosonic`.

-- Generated from ChapterTwoParticleSectorEsa.lean — theorem BookProof.TwoParticleSector.symmetricOn_bosonic
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Mathlib
import Definitions.Def_ChapterTwoParticleSectorEsa
import Theorems.Thm_BookProof_ReducedEsa_commutes_symProj
import Theorems.Thm_BookProof_TwoParticleSector_swapH_mem_sectorDom
import Theorems.Thm_BookProof_TwoParticleSector_sectorOp_swapH
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterTensorGraphCore
import Theorems.Thm_BookProof_TwoParticleSector_isReducingProjection_bosonicProj
import Definitions.Def_ChapterPermutationSectorEsa
open BookProof.TensorCore
open BookProof.TwoParticleSector



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore

noncomputable section

variable (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {X}
variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
variable (A : D₂ →ₗ[ℂ] Hs.carrier)
variable (D : Submodule ℂ Hs.carrier)

theorem BookProof.TwoParticleSector.symmetricOn_bosonic (hA : SymmetricOn D₂ A) :
    @SymmetricOn ↥(sector (bosonicProj Hs)) _ _
      (redDom (bosonicProj Hs) (sectorDom Hs D₂ 2))
      (redOp (sectorOp Hs D₂ A 2) (isReducingProjection_bosonicProj Hs)
        (commutes_symProj (T := sectorOp Hs D₂ A 2)
          (hUD := fun _ hx => swapH_mem_sectorDom Hs D₂ hx) (sectorOp_swapH Hs D₂ A))) := by sorry
