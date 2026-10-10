-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyImprimitivity_mackeyMap_add
-- name    : BookProof.ChapterMackeyImprimitivity.mackeyMap_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:49:51.455736+00:00
-- url     : https://prove2.me/theorems/9eb765c1-1ed3-4086-99c4-241321fbb4d8
-- title:
--   `BookProof.ChapterMackeyImprimitivity.mackeyMap_add` (ψ φ : E) : mackeyMap S s (ψ + φ) = mackeyMap S s ψ + mackeyMap S s φ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMackeyImprimitivity`.
--
--   `BookProof.ChapterMackeyImprimitivity.mackeyMap_add` (ψ φ : E) : mackeyMap S s (ψ + φ) = mackeyMap S s ψ + mackeyMap S s φ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMackeyImprimitivity.mackeyMap_add`.

-- Generated from ChapterMackeyImprimitivity.lean — theorem BookProof.ChapterMackeyImprimitivity.mackeyMap_add
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

theorem BookProof.ChapterMackeyImprimitivity.mackeyMap_add (ψ φ : E) : mackeyMap S s (ψ + φ) = mackeyMap S s ψ + mackeyMap S s φ := by sorry
