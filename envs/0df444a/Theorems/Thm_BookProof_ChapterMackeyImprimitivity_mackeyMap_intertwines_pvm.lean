-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyImprimitivity_mackeyMap_intertwines_pvm
-- name    : BookProof.ChapterMackeyImprimitivity.mackeyMap_intertwines_pvm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:51:46.583096+00:00
-- url     : https://prove2.me/theorems/7deb4bfc-12bb-4e26-a751-019c35c31821
-- title:
--   `BookProof.ChapterMackeyImprimitivity.mackeyMap_intertwines_pvm` [DecidableEq X] (y : X) (ψ : E) : mackeyMap S s (S.p y ψ) = inducedPvm y (mackeyMap S s ψ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMackeyImprimitivity`.
--
--   `BookProof.ChapterMackeyImprimitivity.mackeyMap_intertwines_pvm` [DecidableEq X] (y : X) (ψ : E) : mackeyMap S s (S.p y ψ) = inducedPvm y (mackeyMap S s ψ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMackeyImprimitivity.mackeyMap_intertwines_pvm`.

-- Generated from ChapterMackeyImprimitivity.lean — theorem BookProof.ChapterMackeyImprimitivity.mackeyMap_intertwines_pvm
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

theorem BookProof.ChapterMackeyImprimitivity.mackeyMap_intertwines_pvm [DecidableEq X] (y : X) (ψ : E) :
    mackeyMap S s (S.p y ψ) = inducedPvm y (mackeyMap S s ψ) := by sorry
