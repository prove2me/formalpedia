-- Prove2me | Theorems.Thm_BookProof_ChapterSirkTrotterKato_hasDerivAt_stoneU_const_sub_incr
-- name    : BookProof.ChapterSirkTrotterKato.hasDerivAt_stoneU_const_sub_incr
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:38:25.973651+00:00
-- url     : https://prove2.me/theorems/08698f1d-111a-4331-b624-1de55efe8f8e
-- title:
--   (S : UnboundedSelfAdjoint H) {y : ℝ → H} {y' : H} {t u : ℝ} (hy : HasDerivAt y y' u) : HasDerivAt (fun r : ℝ => S.stoneU (t - r) (y r - y u)) (S.stoneU (t - u) y') u
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkTrotterKato.hasDerivAt_stoneU_const_sub_incr` (module `BookProof.ChapterSirkTrotterKato`), source chapter `BookProof/ChapterChapterSirkTrotterKato.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkTrotterKato.lean

-- Generated from ChapterSirkTrotterKato.lean — theorem BookProof.ChapterSirkTrotterKato.hasDerivAt_stoneU_const_sub_incr
import Mathlib
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterSirkTrotterKato










noncomputable section

open Filter Topology Asymptotics
open scoped InnerProductSpace


open BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem BookProof.ChapterSirkTrotterKato.hasDerivAt_stoneU_const_sub_incr (S : UnboundedSelfAdjoint H) {y : ℝ → H} {y' : H}
    {t u : ℝ} (hy : HasDerivAt y y' u) :
    HasDerivAt (fun r : ℝ => S.stoneU (t - r) (y r - y u)) (S.stoneU (t - u) y') u := by sorry
