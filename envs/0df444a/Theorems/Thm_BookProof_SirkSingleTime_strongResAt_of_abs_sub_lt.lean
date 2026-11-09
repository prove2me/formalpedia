-- Prove2me | Theorems.Thm_BookProof_SirkSingleTime_strongResAt_of_abs_sub_lt
-- name    : BookProof.SirkSingleTime.strongResAt_of_abs_sub_lt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T02:00:11.891453+00:00
-- url     : https://prove2.me/theorems/ec860585-6450-4b21-bcec-72ef102e2030
-- title:
--   `BookProof.SirkSingleTime.strongResAt_of_abs_sub_lt` {l m : ℝ} (hl : l ≠ 0) (hm : m ≠ 0) (hlt : |m - l| < |l|) (h : StrongResAt T S l) : StrongResAt T S m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSirkSingleTimeShift`.
--
--   `BookProof.SirkSingleTime.strongResAt_of_abs_sub_lt` {l m : ℝ} (hl : l ≠ 0) (hm : m ≠ 0) (hlt : |m - l| < |l|) (h : StrongResAt T S l) : StrongResAt T S m
--
--   Formalization note: Lean 4 identifier `BookProof.SirkSingleTime.strongResAt_of_abs_sub_lt`.

-- Generated from ChapterSirkSingleTimeShift.lean — theorem BookProof.SirkSingleTime.strongResAt_of_abs_sub_lt
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

theorem BookProof.SirkSingleTime.strongResAt_of_abs_sub_lt {l m : ℝ} (hl : l ≠ 0) (hm : m ≠ 0)
    (hlt : |m - l| < |l|) (h : StrongResAt T S l) : StrongResAt T S m := by sorry
