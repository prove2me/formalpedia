-- Prove2me | Theorems.Thm_BookProof_ChapterStoneResolvent_UnboundedSelfAdjoint_domain_le_genDomain
-- name    : BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.domain_le_genDomain
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-16T20:28:22.102785+00:00
-- url     : https://prove2.me/theorems/04ff8233-3c0e-4b06-b6ce-9dd074222d29
-- title:
--   The Lean 4 theorem `domain_le_genDomain` in the `ChapterStoneTheorem` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.domain_le_genDomain` from the timepiece Lean 4 formalization: the domain of a self-adjoint operator is contained in the domain of the generator of its unitary group.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterStoneTheorem.lean — theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.domain_le_genDomain
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

theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.domain_le_genDomain (T : UnboundedSelfAdjoint H) :
    T.domain ≤ T.stoneGroup.genDomain := by sorry
