-- Prove2me | solution 1 for term_denotable_finite_support
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:12:25.17044+00:00
-- url     : https://prove2.me/submissions/927682f8-5080-489d-94da-daebaa7d5d15

-- Generated from ChapterPaFreeCompletion.lean — solution of term_denotable_finite_support
import Mathlib
import Definitions.Def_ChapterPaFreeCompletion
import Definitions.Def_ChapterRieszFischer
import Definitions.Def_ChapterA4



open Set
open Filter
open BookProof.ChapterRieszFischer

set_option maxHeartbeats 1000000 in
theorem solution (v : DenseCore) :
    (Function.support (v : ℕ → ℝ)).Finite := Finsupp.finite_support (v : ℕ →₀ ℝ)
