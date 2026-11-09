-- Prove2me | Theorems.Thm_BookProof_SirkSingleTime_strongResAt_neg
-- name    : BookProof.SirkSingleTime.strongResAt_neg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T01:59:44.32139+00:00
-- url     : https://prove2.me/theorems/14fc7160-0edd-43ae-800f-87960b1c4af0
-- title:
--   `BookProof.SirkSingleTime.strongResAt_neg` {l : ℝ} (hl : l ≠ 0) (h : StrongResAt T S l) : StrongResAt T S (-l)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSirkSingleTimeShift`.
--
--   `BookProof.SirkSingleTime.strongResAt_neg` {l : ℝ} (hl : l ≠ 0) (h : StrongResAt T S l) : StrongResAt T S (-l)
--
--   Formalization note: Lean 4 identifier `BookProof.SirkSingleTime.strongResAt_neg`.

-- Generated from ChapterSirkSingleTimeShift.lean — theorem BookProof.SirkSingleTime.strongResAt_neg
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

theorem BookProof.SirkSingleTime.strongResAt_neg {l : ℝ} (hl : l ≠ 0) (h : StrongResAt T S l) :
    StrongResAt T S (-l) := by sorry
