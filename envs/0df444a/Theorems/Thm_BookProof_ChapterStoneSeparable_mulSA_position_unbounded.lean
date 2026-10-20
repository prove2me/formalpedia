-- Prove2me | Theorems.Thm_BookProof_ChapterStoneSeparable_mulSA_position_unbounded
-- name    : BookProof.ChapterStoneSeparable.mulSA_position_unbounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-20T05:01:37.234723+00:00
-- url     : https://prove2.me/theorems/ef1b50ed-bc13-45c1-8446-e8b274128e1f
-- title:
--   `BookProof.ChapterStoneSeparable.mulSA_position_unbounded` : ¬ ∃ C : ℝ, ∀ x : (mulSA positionField).domain, ‖(mulSA positionField).op x‖ ≤ C * ‖(x : L2Z)‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStoneSeparable`.
--
--   `BookProof.ChapterStoneSeparable.mulSA_position_unbounded` : ¬ ∃ C : ℝ, ∀ x : (mulSA positionField).domain, ‖(mulSA positionField).op x‖ ≤ C * ‖(x : L2Z)‖
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterStoneSeparable.mulSA_position_unbounded`.

-- Generated from ChapterStoneSeparable.lean — theorem BookProof.ChapterStoneSeparable.mulSA_position_unbounded
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneConverse
import Mathlib
import Definitions.Def_ChapterStoneSeparable
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterUnboundedPosition
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterUnboundedPosition
open BookProof.ChapterStoneSeparable


open scoped InnerProductSpace
open Filter Topology


open BookProof.ChapterStoneResolvent BookProof.ChapterStoneMeasurable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem BookProof.ChapterStoneSeparable.mulSA_position_unbounded :
    ¬ ∃ C : ℝ, ∀ x : (mulSA positionField).domain,
      ‖(mulSA positionField).op x‖ ≤ C * ‖(x : L2Z)‖ := by sorry
