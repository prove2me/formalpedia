-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyImprimitivity_mackeyMap_intertwines_U
-- name    : BookProof.ChapterMackeyImprimitivity.mackeyMap_intertwines_U
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:51:24.46407+00:00
-- url     : https://prove2.me/theorems/b4a37a01-1f6b-499f-8d6d-c8cd1fa5fb70
-- title:
--   `BookProof.ChapterMackeyImprimitivity.mackeyMap_intertwines_U` (hs : ∀ x, s x • x₀ = x) (g : G) (ψ : E) : mackeyMap S s (S.U g ψ) = inducedRep S s g (mackeyMap S s ψ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMackeyImprimitivity`.
--
--   `BookProof.ChapterMackeyImprimitivity.mackeyMap_intertwines_U` (hs : ∀ x, s x • x₀ = x) (g : G) (ψ : E) : mackeyMap S s (S.U g ψ) = inducedRep S s g (mackeyMap S s ψ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMackeyImprimitivity.mackeyMap_intertwines_U`.

-- Generated from ChapterMackeyImprimitivity.lean — theorem BookProof.ChapterMackeyImprimitivity.mackeyMap_intertwines_U
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

theorem BookProof.ChapterMackeyImprimitivity.mackeyMap_intertwines_U (hs : ∀ x, s x • x₀ = x) (g : G) (ψ : E) :
    mackeyMap S s (S.U g ψ) = inducedRep S s g (mackeyMap S s ψ) := by sorry
