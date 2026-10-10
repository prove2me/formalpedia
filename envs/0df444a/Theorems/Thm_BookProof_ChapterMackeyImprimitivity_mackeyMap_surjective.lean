-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyImprimitivity_mackeyMap_surjective
-- name    : BookProof.ChapterMackeyImprimitivity.mackeyMap_surjective
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:50:48.303338+00:00
-- url     : https://prove2.me/theorems/e820143e-3f95-44c2-8011-ceee18704f60
-- title:
--   `BookProof.ChapterMackeyImprimitivity.mackeyMap_surjective` (hs : ∀ x, s x • x₀ = x) {f : X → E} (hf : f ∈ InducedSpace S x₀) : ∃ ψ : E, mackeyMap S s ψ = f
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMackeyImprimitivity`.
--
--   `BookProof.ChapterMackeyImprimitivity.mackeyMap_surjective` (hs : ∀ x, s x • x₀ = x) {f : X → E} (hf : f ∈ InducedSpace S x₀) : ∃ ψ : E, mackeyMap S s ψ = f
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMackeyImprimitivity.mackeyMap_surjective`.

-- Generated from ChapterMackeyImprimitivity.lean — theorem BookProof.ChapterMackeyImprimitivity.mackeyMap_surjective
import Mathlib
import Definitions.Def_ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity


open scoped InnerProductSpace
open Finset


variable {G : Type*} [Group G] {X : Type*} [Fintype X] [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable (S : ImprimitivitySystem G X E)
variable (S : ImprimitivitySystem G X E) (x₀ : X) (s : X → G)
variable {S x₀ s}

theorem BookProof.ChapterMackeyImprimitivity.mackeyMap_surjective (hs : ∀ x, s x • x₀ = x) {f : X → E}
    (hf : f ∈ InducedSpace S x₀) : ∃ ψ : E, mackeyMap S s ψ = f := by sorry
