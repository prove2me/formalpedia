-- Prove2me | Theorems.Thm_BookProof_ChapterStoneResolvent_UnboundedSelfAdjoint_genDomain_eq_domain
-- name    : BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.genDomain_eq_domain
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T04:59:44.689084+00:00
-- url     : https://prove2.me/theorems/cd2cf99f-69ee-4844-9fcd-c3b8f60358b1
-- title:
--   The Lean 4 theorem `genDomain_eq_domain` in the `ChapterStoneTheorem` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.genDomain_eq_domain` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterStoneTheorem.lean — theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.genDomain_eq_domain
import Mathlib
import Definitions.Def_ChapterStoneTheorem
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup
open BookProof.ChapterStoneResolvent


open scoped InnerProductSpace


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.genDomain_eq_domain (T : UnboundedSelfAdjoint H) :
    T.stoneGroup.genDomain = T.domain := by sorry
