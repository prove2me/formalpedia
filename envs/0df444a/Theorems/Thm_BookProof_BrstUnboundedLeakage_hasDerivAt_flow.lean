-- Prove2me | Theorems.Thm_BookProof_BrstUnboundedLeakage_hasDerivAt_flow
-- name    : BookProof.BrstUnboundedLeakage.hasDerivAt_flow
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:17:36.146286+00:00
-- url     : https://prove2.me/theorems/2e5a3af3-d2aa-43bd-b242-ccf4a5cd4e9a
-- title:
--   `BookProof.BrstUnboundedLeakage.hasDerivAt_flow` (B : H →L[ℂ] H) (x : H) (u : ℝ) : HasDerivAt (fun v : ℝ => flow B v x) ((-Complex.I) • B (flow B u x)) u
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstUnboundedLeakage`.
--
--   `BookProof.BrstUnboundedLeakage.hasDerivAt_flow` (B : H →L[ℂ] H) (x : H) (u : ℝ) : HasDerivAt (fun v : ℝ => flow B v x) ((-Complex.I) • B (flow B u x)) u
--
--   Formalization note: Lean 4 identifier `BookProof.BrstUnboundedLeakage.hasDerivAt_flow`.

-- Generated from ChapterBrstUnboundedLeakage.lean — theorem BookProof.BrstUnboundedLeakage.hasDerivAt_flow
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
import Definitions.Def_ChapterBrstTruncationLeakage
open BookProof.BrstLeakage
open BookProof.BrstUnboundedLeakage


open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem BookProof.BrstUnboundedLeakage.hasDerivAt_flow (B : H →L[ℂ] H) (x : H) (u : ℝ) :
    HasDerivAt (fun v : ℝ => flow B v x) ((-Complex.I) • B (flow B u x)) u := by sorry
