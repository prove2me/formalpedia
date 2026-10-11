-- Prove2me | Theorems.Thm_BookProof_ChapterUnitaryTransport_mulOp_isSelfAdjointOn
-- name    : BookProof.ChapterUnitaryTransport.mulOp_isSelfAdjointOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T08:33:26.477988+00:00
-- url     : https://prove2.me/theorems/b04e52b7-3949-4c85-a58c-bd8fafff5095
-- title:
--   `BookProof.ChapterUnitaryTransport.mulOp_isSelfAdjointOn` (f : ℤ → ℝ) : IsSelfAdjointOn (mulDomain f) (mulOp f)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUnitaryTransport`.
--
--   `BookProof.ChapterUnitaryTransport.mulOp_isSelfAdjointOn` (f : ℤ → ℝ) : IsSelfAdjointOn (mulDomain f) (mulOp f)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterUnitaryTransport.mulOp_isSelfAdjointOn`.

-- Generated from ChapterUnitaryTransport.lean — theorem BookProof.ChapterUnitaryTransport.mulOp_isSelfAdjointOn
import Mathlib
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterUnboundedPosition
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterF7
open BookProof.ChapterUnboundedPosition
open BookProof.ChapterUnitaryTransport


open scoped InnerProductSpace


variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem BookProof.ChapterUnitaryTransport.mulOp_isSelfAdjointOn (f : ℤ → ℝ) : IsSelfAdjointOn (mulDomain f) (mulOp f) := by sorry
