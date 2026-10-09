-- Prove2me | Theorems.Thm_BookProof_BrstUnboundedLeakage_opProj_apply_of_mem
-- name    : BookProof.BrstUnboundedLeakage.opProj_apply_of_mem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T09:48:30.339731+00:00
-- url     : https://prove2.me/theorems/2cfe0d30-ff8a-45fb-bb0f-225d9d8971c8
-- title:
--   `BookProof.BrstUnboundedLeakage.opProj_apply_of_mem` {x : H} (hx : x ∈ V) : opProj T V hV x = T.op ⟨x, hV hx⟩
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstUnboundedLeakage`.
--
--   `BookProof.BrstUnboundedLeakage.opProj_apply_of_mem` {x : H} (hx : x ∈ V) : opProj T V hV x = T.op ⟨x, hV hx⟩
--
--   Formalization note: Lean 4 identifier `BookProof.BrstUnboundedLeakage.opProj_apply_of_mem`.

-- Generated from ChapterBrstUnboundedLeakage.lean — theorem BookProof.BrstUnboundedLeakage.opProj_apply_of_mem
import Definitions.Def_ChapterBrstTruncationLeakage
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
import Definitions.Def_ChapterStoneResolvent
open BookProof.BrstUnboundedLeakage


open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (T : UnboundedSelfAdjoint H)
variable (V : Submodule ℂ H) [FiniteDimensional ℂ V] (hV : V ≤ T.domain)

theorem BookProof.BrstUnboundedLeakage.opProj_apply_of_mem {x : H} (hx : x ∈ V) :
    opProj T V hV x = T.op ⟨x, hV hx⟩ := by sorry
