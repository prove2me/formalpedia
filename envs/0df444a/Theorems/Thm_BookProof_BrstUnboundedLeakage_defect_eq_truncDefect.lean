-- Prove2me | Theorems.Thm_BookProof_BrstUnboundedLeakage_defect_eq_truncDefect
-- name    : BookProof.BrstUnboundedLeakage.defect_eq_truncDefect
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:19:57.363126+00:00
-- url     : https://prove2.me/theorems/1ed599b5-d18b-4f6b-a1e1-e4e4db13b7a0
-- title:
--   `BookProof.BrstUnboundedLeakage.defect_eq_truncDefect` {y : H} (hy : y ∈ V) : T.op ⟨y, hV hy⟩ - truncGen T V hV y = truncDefect T V hV y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstUnboundedLeakage`.
--
--   `BookProof.BrstUnboundedLeakage.defect_eq_truncDefect` {y : H} (hy : y ∈ V) : T.op ⟨y, hV hy⟩ - truncGen T V hV y = truncDefect T V hV y
--
--   Formalization note: Lean 4 identifier `BookProof.BrstUnboundedLeakage.defect_eq_truncDefect`.

-- Generated from ChapterBrstUnboundedLeakage.lean — theorem BookProof.BrstUnboundedLeakage.defect_eq_truncDefect
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

theorem BookProof.BrstUnboundedLeakage.defect_eq_truncDefect {y : H} (hy : y ∈ V) :
    T.op ⟨y, hV hy⟩ - truncGen T V hV y = truncDefect T V hV y := by sorry
