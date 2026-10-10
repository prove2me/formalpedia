-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyImprimitivity_mackeyMap_reconstruct
-- name    : BookProof.ChapterMackeyImprimitivity.mackeyMap_reconstruct
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:51:43.274303+00:00
-- url     : https://prove2.me/theorems/4c52cd06-b60b-4d3c-874c-ab41aaabc6a0
-- title:
--   `BookProof.ChapterMackeyImprimitivity.mackeyMap_reconstruct` (ψ : E) : ∑ x : X, S.U (s x) (mackeyMap S s ψ x) = ψ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMackeyImprimitivity`.
--
--   `BookProof.ChapterMackeyImprimitivity.mackeyMap_reconstruct` (ψ : E) : ∑ x : X, S.U (s x) (mackeyMap S s ψ x) = ψ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMackeyImprimitivity.mackeyMap_reconstruct`.

-- Generated from ChapterMackeyImprimitivity.lean — theorem BookProof.ChapterMackeyImprimitivity.mackeyMap_reconstruct
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

theorem BookProof.ChapterMackeyImprimitivity.mackeyMap_reconstruct (ψ : E) : ∑ x : X, S.U (s x) (mackeyMap S s ψ x) = ψ := by sorry
