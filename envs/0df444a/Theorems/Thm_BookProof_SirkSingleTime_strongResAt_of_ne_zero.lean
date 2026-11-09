-- Prove2me | Theorems.Thm_BookProof_SirkSingleTime_strongResAt_of_ne_zero
-- name    : BookProof.SirkSingleTime.strongResAt_of_ne_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-31T12:36:34.668696+00:00
-- url     : https://prove2.me/theorems/b18afa74-d382-496c-aa38-4648b3e03d9e
-- title:
--   `BookProof.SirkSingleTime.strongResAt_of_ne_zero` {l m : ℝ} (hl : l ≠ 0) (hm : m ≠ 0) (h : StrongResAt T S l) : StrongResAt T S m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSirkSingleTimeShift`.
--
--   `BookProof.SirkSingleTime.strongResAt_of_ne_zero` {l m : ℝ} (hl : l ≠ 0) (hm : m ≠ 0) (h : StrongResAt T S l) : StrongResAt T S m
--
--   Formalization note: Lean 4 identifier `BookProof.SirkSingleTime.strongResAt_of_ne_zero`.

-- Generated from ChapterSirkSingleTimeShift.lean — theorem BookProof.SirkSingleTime.strongResAt_of_ne_zero
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

theorem BookProof.SirkSingleTime.strongResAt_of_ne_zero {l m : ℝ} (hl : l ≠ 0) (hm : m ≠ 0)
    (h : StrongResAt T S l) : StrongResAt T S m := by sorry
