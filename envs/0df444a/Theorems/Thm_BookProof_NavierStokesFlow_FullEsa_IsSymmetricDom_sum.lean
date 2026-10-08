-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_IsSymmetricDom_sum
-- name    : BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T11:38:29.876497+00:00
-- url     : https://prove2.me/theorems/5ba768b9-f5c3-496f-bddf-642fc27ad9e3
-- title:
--   `BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.sum` {ι : Type*} (s : Finset ι) {A : ι → (D →ₗ[ℂ] D)} (hA : ∀ i ∈ s, IsSymmetricDom (A i)) : IsSymmetricDom (∑ i ∈ s, A i)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFullEsa`.
--
--   `BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.sum` {ι : Type*} (s : Finset ι) {A : ι → (D →ₗ[ℂ] D)} (hA : ∀ i ∈ s, IsSymmetricDom (A i)) : IsSymmetricDom (∑ i ∈ s, A i)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.sum`.

-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.sum
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterSirkFinitePrecision
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval
open BookProof.NavierStokesFlow


open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

theorem BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.sum {ι : Type*} (s : Finset ι) {A : ι → (D →ₗ[ℂ] D)}
    (hA : ∀ i ∈ s, IsSymmetricDom (A i)) : IsSymmetricDom (∑ i ∈ s, A i) := by sorry
