-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyGeneralBase_ImprimitivitySystem_inner_pvm_eq_zero
-- name    : BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem.inner_pvm_eq_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T20:21:46.656472+00:00
-- url     : https://prove2.me/theorems/06052153-6dc7-48b0-aa61-d7a9fe482499
-- title:
--   The Lean 4 theorem `inner_pvm_eq_zero` in the `ChapterMackeyGeneralBase` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `inner_pvm_eq_zero` in the `ChapterMackeyGeneralBase` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMackeyGeneralBase.lean

-- Generated from ChapterMackeyGeneralBase.lean — theorem BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem.inner_pvm_eq_zero
import Definitions.Def_ChapterOrthogonalSums
import Mathlib
import Definitions.Def_ChapterMackeyGeneralBase
import Definitions.Def_ChapterMackeyImprimitivity
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterMackeyImprimitivity
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup


open scoped InnerProductSpace


open BookProof.ChapterOrthogonalSums

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable (S : BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem G X E)

theorem BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem.inner_pvm_eq_zero {x y : X} (hxy : x ≠ y) (ψ φ : E) :
    ⟪S.p x ψ, S.p y φ⟫_ℂ = 0 := by sorry
