-- Prove2me | Theorems.Thm_BookProof_PermSector_mem_fermionicSector_iff
-- name    : BookProof.PermSector.mem_fermionicSector_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:51:26.42898+00:00
-- url     : https://prove2.me/theorems/5b5895bd-4cc8-4bf7-84dc-1fcc5f18af3e
-- title:
--   `BookProof.PermSector.mem_fermionicSector_iff` (n : ℕ) {x : (Hs.pow n).carrier} : x ∈ sector (fermionicProj Hs n) ↔ ∀ σ : Equiv.Perm (Fin n), permOp Hs n σ x = ((Equiv.Perm.sign σ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPermutationSectorEsa`.
--
--   `BookProof.PermSector.mem_fermionicSector_iff` (n : ℕ) {x : (Hs.pow n).carrier} : x ∈ sector (fermionicProj Hs n) ↔ ∀ σ : Equiv.Perm (Fin n), permOp Hs n σ x = ((Equiv.Perm.sign σ : ℤ) : ℂ) • x
--
--   Formalization note: Lean 4 identifier `BookProof.PermSector.mem_fermionicSector_iff`.

-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.mem_fermionicSector_iff
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Definitions.Def_ChapterMaschkeFiniteGroup
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterGaugeUnconstrainedSpectrum
open BookProof.ChapterMaschkeFiniteGroup
open BookProof.TensorCore
open BookProof.ChapterWignerLittleGroup
open BookProof.PermSector



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

theorem BookProof.PermSector.mem_fermionicSector_iff (n : ℕ) {x : (Hs.pow n).carrier} :
    x ∈ sector (fermionicProj Hs n)
      ↔ ∀ σ : Equiv.Perm (Fin n),
          permOp Hs n σ x = ((Equiv.Perm.sign σ : ℤ) : ℂ) • x := by sorry
