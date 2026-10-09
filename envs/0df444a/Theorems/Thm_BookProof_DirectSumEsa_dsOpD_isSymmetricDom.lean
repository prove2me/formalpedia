-- Prove2me | Theorems.Thm_BookProof_DirectSumEsa_dsOpD_isSymmetricDom
-- name    : BookProof.DirectSumEsa.dsOpD_isSymmetricDom
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:59:59.58599+00:00
-- url     : https://prove2.me/theorems/1325e995-26a1-4151-92f8-ee65eb6e66ae
-- title:
--   `BookProof.DirectSumEsa.dsOpD_isSymmetricDom` (A : ∀ i, D i →ₗ[ℂ] D i) (hsym : ∀ i, IsSymmetricDom (A i)) : IsSymmetricDom (dsOpD A)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDirectSumEsa`.
--
--   `BookProof.DirectSumEsa.dsOpD_isSymmetricDom` (A : ∀ i, D i →ₗ[ℂ] D i) (hsym : ∀ i, IsSymmetricDom (A i)) : IsSymmetricDom (dsOpD A)
--
--   Formalization note: Lean 4 identifier `BookProof.DirectSumEsa.dsOpD_isSymmetricDom`.

-- Generated from ChapterDirectSumEsa.lean — theorem BookProof.DirectSumEsa.dsOpD_isSymmetricDom
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterNavierStokesFullEsa
open BookProof.NavierStokesFlow.FullEsa
open BookProof.NavierStokesFlow.FullEsa.NSFullData
open BookProof.DirectSumEsa


open scoped ENNReal


open BookProof.FarisLavine

noncomputable section

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]

variable {D : ∀ i, Submodule ℂ (G i)}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
open BookProof.NavierStokesFlow.FullEsa

theorem BookProof.DirectSumEsa.dsOpD_isSymmetricDom (A : ∀ i, D i →ₗ[ℂ] D i)
    (hsym : ∀ i, IsSymmetricDom (A i)) : IsSymmetricDom (dsOpD A) := by sorry
