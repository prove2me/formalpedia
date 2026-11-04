-- Prove2me | Theorems.Thm_BookProof_SirkSingleTime_norm_neg_resCLM_apply_le
-- name    : BookProof.SirkSingleTime.norm_neg_resCLM_apply_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-04T01:59:55.813072+00:00
-- url     : https://prove2.me/theorems/693f14b2-34a8-4fa1-86c3-a460f13f7b7e
-- title:
--   `BookProof.SirkSingleTime.norm_neg_resCLM_apply_le` (T : UnboundedSelfAdjoint E) (l : ℝ) (y : E) : ‖(-(T.resCLM l)) y‖ ≤ (1 / |l|) * ‖y‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSirkSingleTimeShift`.
--
--   `BookProof.SirkSingleTime.norm_neg_resCLM_apply_le` (T : UnboundedSelfAdjoint E) (l : ℝ) (y : E) : ‖(-(T.resCLM l)) y‖ ≤ (1 / |l|) * ‖y‖
--
--   Formalization note: Lean 4 identifier `BookProof.SirkSingleTime.norm_neg_resCLM_apply_le`.

-- Generated from ChapterSirkSingleTimeShift.lean — theorem BookProof.SirkSingleTime.norm_neg_resCLM_apply_le
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterSirkSingleTimeShift
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterQgTimeIndependentFlow
open BookProof.SirkSingleTime


open scoped InnerProductSpace


open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.HashimotoShiftInvert

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {T : UnboundedSelfAdjoint E} {S : ℕ → UnboundedSelfAdjoint E}

theorem BookProof.SirkSingleTime.norm_neg_resCLM_apply_le (T : UnboundedSelfAdjoint E) (l : ℝ) (y : E) :
    ‖(-(T.resCLM l)) y‖ ≤ (1 / |l|) * ‖y‖ := by sorry
