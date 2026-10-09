-- Prove2me | Theorems.Thm_BookProof_BrstUnboundedLeakage_defect_orbit_le
-- name    : BookProof.BrstUnboundedLeakage.defect_orbit_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:41:34.539036+00:00
-- url     : https://prove2.me/theorems/98bb92c2-5f96-4326-9996-a5818cad0961
-- title:
--   `BookProof.BrstUnboundedLeakage.defect_orbit_le` {x : H} (hx : x ∈ V) (s : ℝ) : ‖T.op ⟨flow (truncGen T V hV) s x, flow_truncGen_mem_domain T V hV s hx⟩ - truncGen T V hV (flow (tr
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstUnboundedLeakage`.
--
--   `BookProof.BrstUnboundedLeakage.defect_orbit_le` {x : H} (hx : x ∈ V) (s : ℝ) : ‖T.op ⟨flow (truncGen T V hV) s x, flow_truncGen_mem_domain T V hV s hx⟩ - truncGen T V hV (flow (truncGen T V hV) s x)‖ ≤ ‖truncDefect T V hV‖ * ‖x‖
--
--   Formalization note: Lean 4 identifier `BookProof.BrstUnboundedLeakage.defect_orbit_le`.

-- Generated from ChapterBrstUnboundedLeakage.lean — theorem BookProof.BrstUnboundedLeakage.defect_orbit_le
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
import Definitions.Def_ChapterBrstTruncationLeakage
import Definitions.Def_ChapterStoneResolvent
import Theorems.Thm_BookProof_BrstUnboundedLeakage_flow_truncGen_mem_domain
open BookProof.BrstLeakage
open BookProof.BrstUnboundedLeakage


open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (T : UnboundedSelfAdjoint H)
variable (V : Submodule ℂ H) [FiniteDimensional ℂ V] (hV : V ≤ T.domain)

theorem BookProof.BrstUnboundedLeakage.defect_orbit_le {x : H} (hx : x ∈ V) (s : ℝ) :
    ‖T.op ⟨flow (truncGen T V hV) s x, flow_truncGen_mem_domain T V hV s hx⟩
        - truncGen T V hV (flow (truncGen T V hV) s x)‖ ≤ ‖truncDefect T V hV‖ * ‖x‖ := by sorry
