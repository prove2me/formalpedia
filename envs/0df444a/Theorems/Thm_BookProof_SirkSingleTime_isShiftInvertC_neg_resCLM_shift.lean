-- Prove2me | Theorems.Thm_BookProof_SirkSingleTime_isShiftInvertC_neg_resCLM_shift
-- name    : BookProof.SirkSingleTime.isShiftInvertC_neg_resCLM_shift
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-31T12:36:45.348001+00:00
-- url     : https://prove2.me/theorems/485ed112-a96a-47ef-b498-87c3222f3b94
-- title:
--   `BookProof.SirkSingleTime.isShiftInvertC_neg_resCLM_shift` (T : UnboundedSelfAdjoint E) {l : ℝ} (hl : l ≠ 0) : IsShiftInvertC T.op (((l : ℝ) : ℂ) * Complex.I) (-(T.resCLM l))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSirkSingleTimeShift`.
--
--   `BookProof.SirkSingleTime.isShiftInvertC_neg_resCLM_shift` (T : UnboundedSelfAdjoint E) {l : ℝ} (hl : l ≠ 0) : IsShiftInvertC T.op (((l : ℝ) : ℂ) * Complex.I) (-(T.resCLM l))
--
--   Formalization note: Lean 4 identifier `BookProof.SirkSingleTime.isShiftInvertC_neg_resCLM_shift`.

-- Generated from ChapterSirkSingleTimeShift.lean — theorem BookProof.SirkSingleTime.isShiftInvertC_neg_resCLM_shift
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterSirkSingleTimeShift
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterHashimotoComplexShifts
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterQgTimeIndependentFlow
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.HashimotoShiftInvert
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup
open BookProof.SirkSingleTime


open scoped InnerProductSpace


open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.HashimotoShiftInvert

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {T : UnboundedSelfAdjoint E} {S : ℕ → UnboundedSelfAdjoint E}

theorem BookProof.SirkSingleTime.isShiftInvertC_neg_resCLM_shift (T : UnboundedSelfAdjoint E) {l : ℝ} (hl : l ≠ 0) :
    IsShiftInvertC T.op (((l : ℝ) : ℂ) * Complex.I) (-(T.resCLM l)) := by sorry
