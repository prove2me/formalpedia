-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyGeneralBase_mackeyMap_eq
-- name    : BookProof.ChapterMackeyGeneralBase.mackeyMap_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-04T20:21:58.127182+00:00
-- url     : https://prove2.me/theorems/6a310cec-7f52-451c-9cdd-08d184ca1870
-- title:
--   The Lean 4 theorem `mackeyMap_eq` in the `ChapterMackeyGeneralBase` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `mackeyMap_eq` in the `ChapterMackeyGeneralBase` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMackeyGeneralBase.lean

-- Generated from ChapterMackeyGeneralBase.lean — theorem BookProof.ChapterMackeyGeneralBase.mackeyMap_eq
import Definitions.Def_ChapterOrthogonalSums
import Mathlib
import Definitions.Def_ChapterMackeyGeneralBase
import Definitions.Def_ChapterMackeyImprimitivity
import Definitions.Def_ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity


open scoped InnerProductSpace


open BookProof.ChapterOrthogonalSums

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable (S : BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem G X E)
variable (S : BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem G X E) (x₀ : X) (s : X → G)
variable {S x₀ s}

theorem BookProof.ChapterMackeyGeneralBase.mackeyMap_eq (hs : ∀ x, s x • x₀ = x) (ψ : E) (x : X) :
    mackeyMap S s ψ x = S.p x₀ (S.U (s x)⁻¹ ψ) := by sorry
