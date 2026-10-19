-- Prove2me | Theorems.Thm_BookProof_ChapterUnitaryTransport_adjointDomain_mulOp
-- name    : BookProof.ChapterUnitaryTransport.adjointDomain_mulOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T20:39:05.837983+00:00
-- url     : https://prove2.me/theorems/67d42f7f-efd5-42d4-a73a-97f7ac9938eb
-- title:
--   `BookProof.ChapterUnitaryTransport.adjointDomain_mulOp` (f : ℤ → ℝ) : adjointDomain (mulDomain f) (mulOp f) = BookProof.ChapterUnboundedPosition.adjointDomain f
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUnitaryTransport`.
--
--   `BookProof.ChapterUnitaryTransport.adjointDomain_mulOp` (f : ℤ → ℝ) : adjointDomain (mulDomain f) (mulOp f) = BookProof.ChapterUnboundedPosition.adjointDomain f
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterUnitaryTransport.adjointDomain_mulOp`.

-- Generated from ChapterUnitaryTransport.lean — theorem BookProof.ChapterUnitaryTransport.adjointDomain_mulOp
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

theorem BookProof.ChapterUnitaryTransport.adjointDomain_mulOp (f : ℤ → ℝ) :
    adjointDomain (mulDomain f) (mulOp f) = BookProof.ChapterUnboundedPosition.adjointDomain f := by sorry
