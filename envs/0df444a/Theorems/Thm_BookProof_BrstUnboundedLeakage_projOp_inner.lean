-- Prove2me | Theorems.Thm_BookProof_BrstUnboundedLeakage_projOp_inner
-- name    : BookProof.BrstUnboundedLeakage.projOp_inner
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:22:07.936099+00:00
-- url     : https://prove2.me/theorems/fba9e6b2-fa05-4f04-b77b-2ae3dac19cbd
-- title:
--   `BookProof.BrstUnboundedLeakage.projOp_inner` (x y : H) : ⟪projOp V x, y⟫_ℂ = ⟪x, projOp V y⟫_ℂ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstUnboundedLeakage`.
--
--   `BookProof.BrstUnboundedLeakage.projOp_inner` (x y : H) : ⟪projOp V x, y⟫_ℂ = ⟪x, projOp V y⟫_ℂ
--
--   Formalization note: Lean 4 identifier `BookProof.BrstUnboundedLeakage.projOp_inner`.

-- Generated from ChapterBrstUnboundedLeakage.lean — theorem BookProof.BrstUnboundedLeakage.projOp_inner
import Definitions.Def_ChapterBrstTruncationLeakage
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
open BookProof.BrstUnboundedLeakage


open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (T : UnboundedSelfAdjoint H)
variable (V : Submodule ℂ H) [FiniteDimensional ℂ V] (hV : V ≤ T.domain)

theorem BookProof.BrstUnboundedLeakage.projOp_inner (x y : H) : ⟪projOp V x, y⟫_ℂ = ⟪x, projOp V y⟫_ℂ := by sorry
