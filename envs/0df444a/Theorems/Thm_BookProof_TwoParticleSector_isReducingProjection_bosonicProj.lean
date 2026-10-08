-- Prove2me | Theorems.Thm_BookProof_TwoParticleSector_isReducingProjection_bosonicProj
-- name    : BookProof.TwoParticleSector.isReducingProjection_bosonicProj
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T10:15:39.710116+00:00
-- url     : https://prove2.me/theorems/189f1297-5150-45b8-8836-a04cce4e386b
-- title:
--   `BookProof.TwoParticleSector.isReducingProjection_bosonicProj` : IsReducingProjection (bosonicProj Hs)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTwoParticleSectorEsa`.
--
--   `BookProof.TwoParticleSector.isReducingProjection_bosonicProj` : IsReducingProjection (bosonicProj Hs)
--
--   Formalization note: Lean 4 identifier `BookProof.TwoParticleSector.isReducingProjection_bosonicProj`.

-- Generated from ChapterTwoParticleSectorEsa.lean — theorem BookProof.TwoParticleSector.isReducingProjection_bosonicProj
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Mathlib
import Definitions.Def_ChapterTwoParticleSectorEsa
import Definitions.Def_ChapterTensorGraphCore
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

theorem BookProof.TwoParticleSector.isReducingProjection_bosonicProj : IsReducingProjection (bosonicProj Hs) := by sorry
