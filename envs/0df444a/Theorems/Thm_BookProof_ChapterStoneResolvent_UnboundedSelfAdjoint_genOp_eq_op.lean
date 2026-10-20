-- Prove2me | Theorems.Thm_BookProof_ChapterStoneResolvent_UnboundedSelfAdjoint_genOp_eq_op
-- name    : BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.genOp_eq_op
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-20T01:17:04.202981+00:00
-- url     : https://prove2.me/theorems/d6d07d74-80ee-4713-b3b7-ed86bb3b9abe
-- title:
--   The Lean 4 theorem `genOp_eq_op` in the `ChapterStoneTheorem` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.genOp_eq_op` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterStoneTheorem.lean — theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.genOp_eq_op
import Mathlib
import Definitions.Def_ChapterStoneTheorem
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterSirkTrotterKato
-- `domain_le_genDomain` is carried by this stub (no published def bundle has
-- it — leaf selection dropped it), so `genOp_eq_op`'s statement cannot
-- elaborate without the import
import Theorems.Thm_BookProof_ChapterStoneResolvent_UnboundedSelfAdjoint_domain_le_genDomain
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup
open BookProof.ChapterStoneResolvent


open scoped InnerProductSpace


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.genOp_eq_op (T : UnboundedSelfAdjoint H) (x : T.domain) :
    T.stoneGroup.genOp ⟨(x : H), T.domain_le_genDomain x.2⟩ = T.op x := by sorry
