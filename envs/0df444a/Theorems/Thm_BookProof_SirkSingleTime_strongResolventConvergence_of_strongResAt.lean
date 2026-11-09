-- Prove2me | Theorems.Thm_BookProof_SirkSingleTime_strongResolventConvergence_of_strongResAt
-- name    : BookProof.SirkSingleTime.strongResolventConvergence_of_strongResAt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T01:59:56.40388+00:00
-- url     : https://prove2.me/theorems/0904f53b-ad98-410b-a673-aea3207094ed
-- title:
--   `BookProof.SirkSingleTime.strongResolventConvergence_of_strongResAt` {l : ℝ} (hl : l ≠ 0) (h : StrongResAt T S l) : StrongResolventConvergence T S
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSirkSingleTimeShift`.
--
--   `BookProof.SirkSingleTime.strongResolventConvergence_of_strongResAt` {l : ℝ} (hl : l ≠ 0) (h : StrongResAt T S l) : StrongResolventConvergence T S
--
--   Formalization note: Lean 4 identifier `BookProof.SirkSingleTime.strongResolventConvergence_of_strongResAt`.

-- Generated from ChapterSirkSingleTimeShift.lean — theorem BookProof.SirkSingleTime.strongResolventConvergence_of_strongResAt
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterSirkSingleTimeShift
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterQgTimeIndependentFlow
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.ChapterSirkTrotterKato
open BookProof.ChapterStoneResolvent
open BookProof.ChapterStoneResolvent
open BookProof.SirkSingleTime


open scoped InnerProductSpace


open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.HashimotoShiftInvert

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {T : UnboundedSelfAdjoint E} {S : ℕ → UnboundedSelfAdjoint E}

theorem BookProof.SirkSingleTime.strongResolventConvergence_of_strongResAt {l : ℝ} (hl : l ≠ 0)
    (h : StrongResAt T S l) : StrongResolventConvergence T S := by sorry
