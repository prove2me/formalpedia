-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyImprimitivity_mackeyMap_mem_inducedSpace
-- name    : BookProof.ChapterMackeyImprimitivity.mackeyMap_mem_inducedSpace
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:50:12.002911+00:00
-- url     : https://prove2.me/theorems/f588ff15-b275-439b-bb4e-6737817f6750
-- title:
--   `BookProof.ChapterMackeyImprimitivity.mackeyMap_mem_inducedSpace` (hs : ∀ x, s x • x₀ = x) (ψ : E) : mackeyMap S s ψ ∈ InducedSpace S x₀
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMackeyImprimitivity`.
--
--   `BookProof.ChapterMackeyImprimitivity.mackeyMap_mem_inducedSpace` (hs : ∀ x, s x • x₀ = x) (ψ : E) : mackeyMap S s ψ ∈ InducedSpace S x₀
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMackeyImprimitivity.mackeyMap_mem_inducedSpace`.

-- Generated from ChapterMackeyImprimitivity.lean — theorem BookProof.ChapterMackeyImprimitivity.mackeyMap_mem_inducedSpace
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

theorem BookProof.ChapterMackeyImprimitivity.mackeyMap_mem_inducedSpace (hs : ∀ x, s x • x₀ = x) (ψ : E) :
    mackeyMap S s ψ ∈ InducedSpace S x₀ := by sorry
