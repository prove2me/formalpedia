-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyImprimitivity_mackeyMap_injective
-- name    : BookProof.ChapterMackeyImprimitivity.mackeyMap_injective
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:50:53.86301+00:00
-- url     : https://prove2.me/theorems/f0c2ec5e-4b39-4aaf-8b1d-ed02b4bfd0a6
-- title:
--   `BookProof.ChapterMackeyImprimitivity.mackeyMap_injective` : Function.Injective (mackeyMap S s)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMackeyImprimitivity`.
--
--   `BookProof.ChapterMackeyImprimitivity.mackeyMap_injective` : Function.Injective (mackeyMap S s)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMackeyImprimitivity.mackeyMap_injective`.

-- Generated from ChapterMackeyImprimitivity.lean — theorem BookProof.ChapterMackeyImprimitivity.mackeyMap_injective
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

theorem BookProof.ChapterMackeyImprimitivity.mackeyMap_injective : Function.Injective (mackeyMap S s) := by sorry
