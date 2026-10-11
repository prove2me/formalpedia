-- Prove2me | solution 1 for riesz_fischer
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T00:10:45.401707+00:00
-- url     : https://prove2.me/submissions/eb297f75-41e1-4cb6-a136-82978bd4d253

-- Generated from ChapterPaFreeCompletion.lean — solution of riesz_fischer
import Mathlib
import Definitions.Def_ChapterPaFreeCompletion
import Theorems.Thm_BookProof_ChapterRieszFischer_ell2_completeSpace
import Theorems.Thm_BookProof_ChapterRieszFischer_riesz_fischer_hasSum
import Definitions.Def_ChapterRieszFischer
import Definitions.Def_ChapterA4



open Set
open Filter
open BookProof.ChapterRieszFischer

set_option maxHeartbeats 1000000 in
theorem solution :
    CompleteSpace Ell2 ∧
      ∀ f : Ell2, HasSum (fun i => lp.single 2 i ((f : ℕ → ℝ) i)) f := ⟨ell2_completeSpace, riesz_fischer_hasSum⟩
