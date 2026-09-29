-- Prove2me | Theorems.Thm_BookProof_ChapterSirkTrotterKato_hasDerivAt_stoneU_const_sub_apply
-- name    : BookProof.ChapterSirkTrotterKato.hasDerivAt_stoneU_const_sub_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:55:02.813722+00:00
-- url     : https://prove2.me/theorems/a5740adb-5dc1-43e1-8a4b-1d1636448acf
-- title:
--   (S : UnboundedSelfAdjoint H) {y : ℝ → H} {y' : H} {t u : ℝ} (hy : HasDerivAt y y' u) (hmem : y u ∈ S.domain) : HasDerivAt (fun r : ℝ => S.stoneU (t - r) (y r)) (Complex.I • S.op...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkTrotterKato.hasDerivAt_stoneU_const_sub_apply` (module `BookProof.ChapterSirkTrotterKato`), source chapter `BookProof/ChapterChapterSirkTrotterKato.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkTrotterKato.lean

-- Generated from ChapterSirkTrotterKato.lean — theorem BookProof.ChapterSirkTrotterKato.hasDerivAt_stoneU_const_sub_apply
import Mathlib
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterSirkTrotterKato










noncomputable section

open Filter Topology Asymptotics
open scoped InnerProductSpace


open BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem BookProof.ChapterSirkTrotterKato.hasDerivAt_stoneU_const_sub_apply (S : UnboundedSelfAdjoint H) {y : ℝ → H} {y' : H}
    {t u : ℝ} (hy : HasDerivAt y y' u) (hmem : y u ∈ S.domain) :
    HasDerivAt (fun r : ℝ => S.stoneU (t - r) (y r))
      (Complex.I • S.op ⟨S.stoneU (t - u) (y u), S.stoneU_mem_domain (t - u) ⟨y u, hmem⟩⟩
        + S.stoneU (t - u) y') u := by sorry
