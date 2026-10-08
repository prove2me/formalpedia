-- Prove2me | Theorems.Thm_BookProof_BrstUnboundedLeakage_proj_mul_truncGen
-- name    : BookProof.BrstUnboundedLeakage.proj_mul_truncGen
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:19:51.239995+00:00
-- url     : https://prove2.me/theorems/3f12c285-c04b-489e-8c9a-ab9f5ffdca2d
-- title:
--   `BookProof.BrstUnboundedLeakage.proj_mul_truncGen` : projOp V * truncGen T V hV = truncGen T V hV
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstUnboundedLeakage`.
--
--   `BookProof.BrstUnboundedLeakage.proj_mul_truncGen` : projOp V * truncGen T V hV = truncGen T V hV
--
--   Formalization note: Lean 4 identifier `BookProof.BrstUnboundedLeakage.proj_mul_truncGen`.

-- Generated from ChapterBrstUnboundedLeakage.lean — theorem BookProof.BrstUnboundedLeakage.proj_mul_truncGen
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

theorem BookProof.BrstUnboundedLeakage.proj_mul_truncGen : projOp V * truncGen T V hV = truncGen T V hV := by sorry
