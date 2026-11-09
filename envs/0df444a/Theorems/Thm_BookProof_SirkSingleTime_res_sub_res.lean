-- Prove2me | Theorems.Thm_BookProof_SirkSingleTime_res_sub_res
-- name    : BookProof.SirkSingleTime.res_sub_res
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T01:59:59.017307+00:00
-- url     : https://prove2.me/theorems/63525e8a-9fb4-441c-a9a1-a98641fbf20e
-- title:
--   `BookProof.SirkSingleTime.res_sub_res` (T : UnboundedSelfAdjoint E) {l m : ℝ} (hl : l ≠ 0) (hm : m ≠ 0) (y : E) : ((T.res l y : T.domain) : E) - ((T.res m y : T.domain) : E) = (((l
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSirkSingleTimeShift`.
--
--   `BookProof.SirkSingleTime.res_sub_res` (T : UnboundedSelfAdjoint E) {l m : ℝ} (hl : l ≠ 0) (hm : m ≠ 0) (y : E) : ((T.res l y : T.domain) : E) - ((T.res m y : T.domain) : E) = (((l - m : ℝ) : ℂ) * Complex.I) • ((T.res l ((T.res m y : T.domain) : E) : T.domain) : E)
--
--   Formalization note: Lean 4 identifier `BookProof.SirkSingleTime.res_sub_res`.

-- Generated from ChapterSirkSingleTimeShift.lean — theorem BookProof.SirkSingleTime.res_sub_res
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

theorem BookProof.SirkSingleTime.res_sub_res (T : UnboundedSelfAdjoint E) {l m : ℝ} (hl : l ≠ 0) (hm : m ≠ 0) (y : E) :
    ((T.res l y : T.domain) : E) - ((T.res m y : T.domain) : E)
      = (((l - m : ℝ) : ℂ) * Complex.I) •
          ((T.res l ((T.res m y : T.domain) : E) : T.domain) : E) := by sorry
