-- Prove2me | Theorems.Thm_BookProof_PermSector_isReducingProjection_fermionicProj
-- name    : BookProof.PermSector.isReducingProjection_fermionicProj
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T19:44:48.732977+00:00
-- url     : https://prove2.me/theorems/34f779b6-ffac-43c8-a3bf-f332c8534750
-- title:
--   `BookProof.PermSector.isReducingProjection_fermionicProj` (n : ℕ) : IsReducingProjection (fermionicProj Hs n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPermutationSectorEsa`.
--
--   `BookProof.PermSector.isReducingProjection_fermionicProj` (n : ℕ) : IsReducingProjection (fermionicProj Hs n)
--
--   Formalization note: Lean 4 identifier `BookProof.PermSector.isReducingProjection_fermionicProj`.

-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.isReducingProjection_fermionicProj
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Definitions.Def_ChapterTensorGraphCore
open BookProof.ChapterGaugeUnconstrainedSpectrum
open BookProof.TensorCore
open BookProof.PermSector



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

theorem BookProof.PermSector.isReducingProjection_fermionicProj (n : ℕ) :
    IsReducingProjection (fermionicProj Hs n) := by sorry
