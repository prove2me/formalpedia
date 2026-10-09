-- Prove2me | Theorems.Thm_BookProof_ChapterH5_norm_rankOneProj_le
-- name    : BookProof.ChapterH5.norm_rankOneProj_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:53:18.102251+00:00
-- url     : https://prove2.me/theorems/0a5fa013-904f-47ea-8a86-03951471dd1b
-- title:
--   `BookProof.ChapterH5.norm_rankOneProj_le` (u : E) : ‖rankOneProj u‖ ≤ ‖u‖ * ‖u‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterH5`.
--
--   `BookProof.ChapterH5.norm_rankOneProj_le` (u : E) : ‖rankOneProj u‖ ≤ ‖u‖ * ‖u‖
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterH5.norm_rankOneProj_le`.

-- Generated from ChapterH5.lean — theorem BookProof.ChapterH5.norm_rankOneProj_le
import Mathlib
import Definitions.Def_ChapterH5
open BookProof.ChapterH5


noncomputable section



variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

variable {H : E →ₗ[K] E} {v : E}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterH5.norm_rankOneProj_le (u : E) : ‖rankOneProj u‖ ≤ ‖u‖ * ‖u‖ := by sorry
