-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyImprimitivity_mackeyMap_eq
-- name    : BookProof.ChapterMackeyImprimitivity.mackeyMap_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:49:47.112841+00:00
-- url     : https://prove2.me/theorems/2289e58a-deea-449f-ae15-b7a76813a25e
-- title:
--   `BookProof.ChapterMackeyImprimitivity.mackeyMap_eq` (hs : ∀ x, s x • x₀ = x) (ψ : E) (x : X) : mackeyMap S s ψ x = S.p x₀ (S.U (s x)⁻¹ ψ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMackeyImprimitivity`.
--
--   `BookProof.ChapterMackeyImprimitivity.mackeyMap_eq` (hs : ∀ x, s x • x₀ = x) (ψ : E) (x : X) : mackeyMap S s ψ x = S.p x₀ (S.U (s x)⁻¹ ψ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMackeyImprimitivity.mackeyMap_eq`.

-- Generated from ChapterMackeyImprimitivity.lean — theorem BookProof.ChapterMackeyImprimitivity.mackeyMap_eq
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

theorem BookProof.ChapterMackeyImprimitivity.mackeyMap_eq (hs : ∀ x, s x • x₀ = x) (ψ : E) (x : X) :
    mackeyMap S s ψ x = S.p x₀ (S.U (s x)⁻¹ ψ) := by sorry
