-- Prove2me | Theorems.Thm_BookProof_ChapterStoneResolvent_UnboundedSelfAdjoint_ext_prime
-- name    : BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.ext_prime
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T04:57:39.035179+00:00
-- url     : https://prove2.me/theorems/d8d576f5-8bb0-49d0-86a8-4ccd712f2d48
-- title:
--   The Lean 4 theorem `ext_prime` in the `ChapterStoneTheorem` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.ext_prime` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterStoneTheorem.lean — theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.ext'
import Mathlib
import Definitions.Def_ChapterStoneTheorem
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterUnitaryTransport
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


open scoped InnerProductSpace

theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.ext_prime : ∀ {T S : UnboundedSelfAdjoint H}, T.domain = S.domain →
    (∀ (x : H) (hx : x ∈ T.domain) (hx' : x ∈ S.domain), T.op ⟨x, hx⟩ = S.op ⟨x, hx'⟩) → T = S := by sorry
