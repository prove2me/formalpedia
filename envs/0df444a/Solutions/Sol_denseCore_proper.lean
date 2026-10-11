-- Prove2me | solution 1 for denseCore_proper
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T00:10:48.098419+00:00
-- url     : https://prove2.me/submissions/5a327d4c-965f-45d0-99f2-0ed3316cd0aa

-- Generated from ChapterPaFreeCompletion.lean — solution of denseCore_proper
import Mathlib
import Definitions.Def_ChapterPaFreeCompletion
import Theorems.Thm_range_ofCore
import Theorems.Thm_BookProof_ChapterRieszFischer_finSupport_ne_univ
import Definitions.Def_ChapterRieszFischer
import Definitions.Def_ChapterA4



open Set
open Filter
open BookProof.ChapterRieszFischer

set_option maxHeartbeats 1000000 in
theorem solution : Set.range ofCore ≠ (Set.univ : Set Ell2) := by

  rw [range_ofCore]; exact finSupport_ne_univ
