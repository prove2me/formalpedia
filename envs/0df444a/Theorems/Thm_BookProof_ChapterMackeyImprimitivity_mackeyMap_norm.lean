-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyImprimitivity_mackeyMap_norm
-- name    : BookProof.ChapterMackeyImprimitivity.mackeyMap_norm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:50:25.114184+00:00
-- url     : https://prove2.me/theorems/039c4b5a-7f47-4c94-b764-1cf8232cf3ee
-- title:
--   `BookProof.ChapterMackeyImprimitivity.mackeyMap_norm` (ψ : E) (x : X) : ‖mackeyMap S s ψ x‖ = ‖S.p x ψ‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMackeyImprimitivity`.
--
--   `BookProof.ChapterMackeyImprimitivity.mackeyMap_norm` (ψ : E) (x : X) : ‖mackeyMap S s ψ x‖ = ‖S.p x ψ‖
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMackeyImprimitivity.mackeyMap_norm`.

-- Generated from ChapterMackeyImprimitivity.lean — theorem BookProof.ChapterMackeyImprimitivity.mackeyMap_norm
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

theorem BookProof.ChapterMackeyImprimitivity.mackeyMap_norm (ψ : E) (x : X) : ‖mackeyMap S s ψ x‖ = ‖S.p x ψ‖ := by sorry
