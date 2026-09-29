-- Prove2me | Theorems.Thm_BookProof_ChapterSirkTrotterKato_trotterKato_tendstoUniformlyOn
-- name    : BookProof.ChapterSirkTrotterKato.trotterKato_tendstoUniformlyOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T06:04:19.78703+00:00
-- url     : https://prove2.me/theorems/eba32871-1816-46c7-a5ff-ba6aff87004f
-- title:
--   (hres : StrongResolventConvergence T S) (v : H) {T₀ : ℝ} (hT₀ : 0 ≤ T₀) : TendstoUniformlyOn (fun n t => (S n).stoneU t v) (fun t => T.stoneU t v) atTop (Set.Icc (-T₀) T₀)
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkTrotterKato.trotterKato_tendstoUniformlyOn` (module `BookProof.ChapterSirkTrotterKato`), source chapter `BookProof/ChapterChapterSirkTrotterKato.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkTrotterKato.lean

-- Generated from ChapterSirkTrotterKato.lean — theorem BookProof.ChapterSirkTrotterKato.trotterKato_tendstoUniformlyOn
import Mathlib
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterSirkTrotterKato










noncomputable section

open Filter Topology Asymptotics
open scoped InnerProductSpace


open BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]













variable (T : UnboundedSelfAdjoint H) (S : ℕ → UnboundedSelfAdjoint H)

theorem BookProof.ChapterSirkTrotterKato.trotterKato_tendstoUniformlyOn (hres : StrongResolventConvergence T S) (v : H)
    {T₀ : ℝ} (hT₀ : 0 ≤ T₀) :
    TendstoUniformlyOn (fun n t => (S n).stoneU t v) (fun t => T.stoneU t v) atTop
      (Set.Icc (-T₀) T₀) := by sorry
