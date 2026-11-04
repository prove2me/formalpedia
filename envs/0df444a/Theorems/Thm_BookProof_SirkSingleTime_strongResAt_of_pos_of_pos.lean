-- Prove2me | Theorems.Thm_BookProof_SirkSingleTime_strongResAt_of_pos_of_pos
-- name    : BookProof.SirkSingleTime.strongResAt_of_pos_of_pos
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-04T02:00:34.306343+00:00
-- url     : https://prove2.me/theorems/0e375cd3-9583-4ae6-ba19-76836242fd1c
-- title:
--   `BookProof.SirkSingleTime.strongResAt_of_pos_of_pos` {l m : ℝ} (hl : 0 < l) (hm : 0 < m) (h : StrongResAt T S l) : StrongResAt T S m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSirkSingleTimeShift`.
--
--   `BookProof.SirkSingleTime.strongResAt_of_pos_of_pos` {l m : ℝ} (hl : 0 < l) (hm : 0 < m) (h : StrongResAt T S l) : StrongResAt T S m
--
--   Formalization note: Lean 4 identifier `BookProof.SirkSingleTime.strongResAt_of_pos_of_pos`.

-- Generated from ChapterSirkSingleTimeShift.lean — theorem BookProof.SirkSingleTime.strongResAt_of_pos_of_pos
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

theorem BookProof.SirkSingleTime.strongResAt_of_pos_of_pos {l m : ℝ} (hl : 0 < l) (hm : 0 < m)
    (h : StrongResAt T S l) : StrongResAt T S m := by sorry
