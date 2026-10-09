-- Prove2me | Theorems.Thm_BookProof_BrstUnboundedLeakage_flow_truncGen_mem_domain
-- name    : BookProof.BrstUnboundedLeakage.flow_truncGen_mem_domain
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T10:12:14.107542+00:00
-- url     : https://prove2.me/theorems/b6a8e589-488a-4bd0-8518-281dfd44ffd5
-- title:
--   `BookProof.BrstUnboundedLeakage.flow_truncGen_mem_domain` (t : ℝ) {x : H} (hx : x ∈ V) : flow (truncGen T V hV) t x ∈ T.domain
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstUnboundedLeakage`.
--
--   `BookProof.BrstUnboundedLeakage.flow_truncGen_mem_domain` (t : ℝ) {x : H} (hx : x ∈ V) : flow (truncGen T V hV) t x ∈ T.domain
--
--   Formalization note: Lean 4 identifier `BookProof.BrstUnboundedLeakage.flow_truncGen_mem_domain`.

-- Generated from ChapterBrstUnboundedLeakage.lean — theorem BookProof.BrstUnboundedLeakage.flow_truncGen_mem_domain
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
import Definitions.Def_ChapterBrstTruncationLeakage
import Definitions.Def_ChapterStoneResolvent
open BookProof.BrstLeakage
open BookProof.BrstUnboundedLeakage


open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (T : UnboundedSelfAdjoint H)
variable (V : Submodule ℂ H) [FiniteDimensional ℂ V] (hV : V ≤ T.domain)

theorem BookProof.BrstUnboundedLeakage.flow_truncGen_mem_domain (t : ℝ) {x : H} (hx : x ∈ V) :
    flow (truncGen T V hV) t x ∈ T.domain := by sorry
