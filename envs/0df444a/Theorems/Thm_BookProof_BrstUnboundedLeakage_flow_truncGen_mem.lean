-- Prove2me | Theorems.Thm_BookProof_BrstUnboundedLeakage_flow_truncGen_mem
-- name    : BookProof.BrstUnboundedLeakage.flow_truncGen_mem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T10:57:02.269004+00:00
-- url     : https://prove2.me/theorems/773b8f53-c313-4dd5-9623-0c58ededee47
-- title:
--   `BookProof.BrstUnboundedLeakage.flow_truncGen_mem` (t : ℝ) {x : H} (hx : x ∈ V) : flow (truncGen T V hV) t x ∈ V
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstUnboundedLeakage`.
--
--   `BookProof.BrstUnboundedLeakage.flow_truncGen_mem` (t : ℝ) {x : H} (hx : x ∈ V) : flow (truncGen T V hV) t x ∈ V
--
--   Formalization note: Lean 4 identifier `BookProof.BrstUnboundedLeakage.flow_truncGen_mem`.

-- Generated from ChapterBrstUnboundedLeakage.lean — theorem BookProof.BrstUnboundedLeakage.flow_truncGen_mem
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

theorem BookProof.BrstUnboundedLeakage.flow_truncGen_mem (t : ℝ) {x : H} (hx : x ∈ V) : flow (truncGen T V hV) t x ∈ V := by sorry
