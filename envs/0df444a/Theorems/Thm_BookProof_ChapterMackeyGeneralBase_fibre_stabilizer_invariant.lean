-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyGeneralBase_fibre_stabilizer_invariant
-- name    : BookProof.ChapterMackeyGeneralBase.fibre_stabilizer_invariant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T20:21:21.728519+00:00
-- url     : https://prove2.me/theorems/2130fd5c-2482-4373-a04f-2134fe5accac
-- title:
--   The Lean 4 theorem `fibre_stabilizer_invariant` in the `ChapterMackeyGeneralBase` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `fibre_stabilizer_invariant` in the `ChapterMackeyGeneralBase` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMackeyGeneralBase.lean

-- Generated from ChapterMackeyGeneralBase.lean — theorem BookProof.ChapterMackeyGeneralBase.fibre_stabilizer_invariant
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

theorem BookProof.ChapterMackeyGeneralBase.fibre_stabilizer_invariant {h : G} (hh : h ∈ MulAction.stabilizer G x₀) {v : E}
    (hv : S.p x₀ v = v) : S.p x₀ (S.U h v) = S.U h v := by sorry
