-- Prove2me | solution 1 for denseCore_dense
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T00:10:46.661449+00:00
-- url     : https://prove2.me/submissions/a361b5da-9f30-4299-99b8-be2990d2705a

-- Generated from ChapterPaFreeCompletion.lean — solution of denseCore_dense
import Mathlib
import Definitions.Def_ChapterPaFreeCompletion
import Theorems.Thm_range_ofCore
import Theorems.Thm_BookProof_ChapterRieszFischer_finSupport_dense
import Definitions.Def_ChapterRieszFischer
import Definitions.Def_ChapterA4



open Set
open Filter
open BookProof.ChapterRieszFischer

set_option maxHeartbeats 1000000 in
theorem solution : Dense (Set.range ofCore) := by

  rw [range_ofCore]; exact finSupport_dense
