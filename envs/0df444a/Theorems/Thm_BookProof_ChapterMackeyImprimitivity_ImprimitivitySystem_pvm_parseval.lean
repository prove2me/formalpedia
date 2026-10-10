-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyImprimitivity_ImprimitivitySystem_pvm_parseval
-- name    : BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem.pvm_parseval
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:49:47.856518+00:00
-- url     : https://prove2.me/theorems/b8032741-990e-49cc-9234-07af3e0fcddf
-- title:
--   `BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem.pvm_parseval` (ψ : E) : ∑ x : X, ‖S.p x ψ‖ ^ 2 = ‖ψ‖ ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMackeyImprimitivity`.
--
--   `BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem.pvm_parseval` (ψ : E) : ∑ x : X, ‖S.p x ψ‖ ^ 2 = ‖ψ‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem.pvm_parseval`.

-- Generated from ChapterMackeyImprimitivity.lean — theorem BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem.pvm_parseval
import Mathlib
import Definitions.Def_ChapterMackeyImprimitivity
import Definitions.Def_ChapterStoneConverse
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup
open BookProof.ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity


open scoped InnerProductSpace
open Finset


variable {G : Type*} [Group G] {X : Type*} [Fintype X] [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable (S : ImprimitivitySystem G X E)

theorem BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem.pvm_parseval (ψ : E) : ∑ x : X, ‖S.p x ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by sorry
