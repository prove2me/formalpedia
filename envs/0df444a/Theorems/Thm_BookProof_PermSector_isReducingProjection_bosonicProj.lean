-- Prove2me | Theorems.Thm_BookProof_PermSector_isReducingProjection_bosonicProj
-- name    : BookProof.PermSector.isReducingProjection_bosonicProj
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T19:44:35.181759+00:00
-- url     : https://prove2.me/theorems/5e40f620-2037-4669-aa55-84bb5ebf1fd9
-- title:
--   `BookProof.PermSector.isReducingProjection_bosonicProj` (n : ℕ) : IsReducingProjection (bosonicProj Hs n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPermutationSectorEsa`.
--
--   `BookProof.PermSector.isReducingProjection_bosonicProj` (n : ℕ) : IsReducingProjection (bosonicProj Hs n)
--
--   Formalization note: Lean 4 identifier `BookProof.PermSector.isReducingProjection_bosonicProj`.

-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.isReducingProjection_bosonicProj
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterTensorGraphCore
open BookProof.TensorCore
open BookProof.PermSector



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

theorem BookProof.PermSector.isReducingProjection_bosonicProj (n : ℕ) : IsReducingProjection (bosonicProj Hs n) := by sorry
