-- Prove2me | Theorems.Thm_BookProof_SirkSingleTime_norm_res_neg
-- name    : BookProof.SirkSingleTime.norm_res_neg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T02:00:05.674309+00:00
-- url     : https://prove2.me/theorems/d89ba391-8e7f-417d-8258-567b3a1267c3
-- title:
--   `BookProof.SirkSingleTime.norm_res_neg` (T : UnboundedSelfAdjoint E) {l : ℝ} (hl : l ≠ 0) (y : E) : ‖((T.res (-l) y : T.domain) : E)‖ = ‖((T.res l y : T.domain) : E)‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSirkSingleTimeShift`.
--
--   `BookProof.SirkSingleTime.norm_res_neg` (T : UnboundedSelfAdjoint E) {l : ℝ} (hl : l ≠ 0) (y : E) : ‖((T.res (-l) y : T.domain) : E)‖ = ‖((T.res l y : T.domain) : E)‖
--
--   Formalization note: Lean 4 identifier `BookProof.SirkSingleTime.norm_res_neg`.

-- Generated from ChapterSirkSingleTimeShift.lean — theorem BookProof.SirkSingleTime.norm_res_neg
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

theorem BookProof.SirkSingleTime.norm_res_neg (T : UnboundedSelfAdjoint E) {l : ℝ} (hl : l ≠ 0) (y : E) :
    ‖((T.res (-l) y : T.domain) : E)‖ = ‖((T.res l y : T.domain) : E)‖ := by sorry
