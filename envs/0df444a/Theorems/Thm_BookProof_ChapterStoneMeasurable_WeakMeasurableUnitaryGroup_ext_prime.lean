-- Prove2me | Theorems.Thm_BookProof_ChapterStoneMeasurable_WeakMeasurableUnitaryGroup_ext_prime
-- name    : BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.ext_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T09:58:06.134135+00:00
-- url     : https://prove2.me/theorems/d7808ce1-02aa-4d94-bfb8-c4985a7f7bc0
-- title:
--   The Lean 4 theorem `ext_prime` in the `ChapterStoneTheorem` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.ext_prime` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterStoneTheorem.lean — theorem BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.ext'
import Mathlib
import Definitions.Def_ChapterStoneTheorem
import Definitions.Def_ChapterStoneMeasurable
import Definitions.Def_ChapterStoneConverse
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]


open scoped InnerProductSpace

theorem BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.ext_prime :
    ∀ {G G' : WeakMeasurableUnitaryGroup H}, (∀ t, G.U t = G'.U t) → G = G' := by sorry
