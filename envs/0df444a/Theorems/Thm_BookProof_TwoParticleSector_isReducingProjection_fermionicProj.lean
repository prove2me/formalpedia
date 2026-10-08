-- Prove2me | Theorems.Thm_BookProof_TwoParticleSector_isReducingProjection_fermionicProj
-- name    : BookProof.TwoParticleSector.isReducingProjection_fermionicProj
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T10:15:46.27477+00:00
-- url     : https://prove2.me/theorems/40866d21-858f-4e8c-bbe4-b90caae9254c
-- title:
--   `BookProof.TwoParticleSector.isReducingProjection_fermionicProj` : IsReducingProjection (fermionicProj Hs)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTwoParticleSectorEsa`.
--
--   `BookProof.TwoParticleSector.isReducingProjection_fermionicProj` : IsReducingProjection (fermionicProj Hs)
--
--   Formalization note: Lean 4 identifier `BookProof.TwoParticleSector.isReducingProjection_fermionicProj`.

-- Generated from ChapterTwoParticleSectorEsa.lean — theorem BookProof.TwoParticleSector.isReducingProjection_fermionicProj
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

theorem BookProof.TwoParticleSector.isReducingProjection_fermionicProj : IsReducingProjection (fermionicProj Hs) := by sorry
