-- Prove2me | Theorems.Thm_BookProof_TwoParticleSector_essentiallySelfAdjointOn_bosonic
-- name    : BookProof.TwoParticleSector.essentiallySelfAdjointOn_bosonic
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-09T17:55:35.129228+00:00
-- url     : https://prove2.me/theorems/b1135b3c-5bc7-4ae8-a41e-8049c1ba3efa
-- title:
--   `BookProof.TwoParticleSector.essentiallySelfAdjointOn_bosonic` (hesa : EssentiallySelfAdjointOn (sectorDom Hs D₂ 2) (sectorOp Hs D₂ A 2)) : EssentiallySelfAdjointOn (redDom (bosoni
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTwoParticleSectorEsa`.
--
--   `BookProof.TwoParticleSector.essentiallySelfAdjointOn_bosonic` (hesa : EssentiallySelfAdjointOn (sectorDom Hs D₂ 2) (sectorOp Hs D₂ A 2)) : EssentiallySelfAdjointOn (redDom (bosonicProj Hs) (sectorDom Hs D₂ 2)) (redOp (sectorOp Hs D₂ A 2) (isReducingProjection_bosonicProj Hs) (commutes_symProj (T := sectorOp Hs D₂ A 2) (hUD := fun _ hx => swapH_mem_sectorDom Hs D₂ hx) (sectorOp_swapH Hs D₂ A)))
--
--   Formalization note: Lean 4 identifier `BookProof.TwoParticleSector.essentiallySelfAdjointOn_bosonic`.

-- Generated from ChapterTwoParticleSectorEsa.lean — theorem BookProof.TwoParticleSector.essentiallySelfAdjointOn_bosonic
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Mathlib
import Definitions.Def_ChapterTwoParticleSectorEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterTensorGraphCore
import Theorems.Thm_BookProof_TwoParticleSector_isReducingProjection_bosonicProj
import Definitions.Def_ChapterPermutationSectorEsa
import Theorems.Thm_BookProof_ReducedEsa_commutes_symProj
import Theorems.Thm_BookProof_TwoParticleSector_swapH_mem_sectorDom
import Theorems.Thm_BookProof_TwoParticleSector_sectorOp_swapH
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

theorem BookProof.TwoParticleSector.essentiallySelfAdjointOn_bosonic
    (hesa : EssentiallySelfAdjointOn (sectorDom Hs D₂ 2) (sectorOp Hs D₂ A 2)) :
    EssentiallySelfAdjointOn (F := sector (bosonicProj Hs))
      (redDom (bosonicProj Hs) (sectorDom Hs D₂ 2))
      (redOp (sectorOp Hs D₂ A 2) (isReducingProjection_bosonicProj Hs)
        (commutes_symProj (T := sectorOp Hs D₂ A 2)
          (hUD := fun _ hx => swapH_mem_sectorDom Hs D₂ hx) (sectorOp_swapH Hs D₂ A))) := by sorry
