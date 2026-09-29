-- Prove2me | Theorems.Thm_BookProof_ChapterSirkTrotterKato_trotterKato_tendsto
-- name    : BookProof.ChapterSirkTrotterKato.trotterKato_tendsto
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T06:03:42.347163+00:00
-- url     : https://prove2.me/theorems/ce36cac9-75c2-4e3c-b5a3-caceba7cd244
-- title:
--   (hres : StrongResolventConvergence T S) (v : H) (t : ℝ) : Tendsto (fun n => (S n).stoneU t v) atTop (𝓝 (T.stoneU t v))
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkTrotterKato.trotterKato_tendsto` (module `BookProof.ChapterSirkTrotterKato`), source chapter `BookProof/ChapterChapterSirkTrotterKato.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkTrotterKato.lean

-- Generated from ChapterSirkTrotterKato.lean — theorem BookProof.ChapterSirkTrotterKato.trotterKato_tendsto
import Mathlib
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterSirkTrotterKato










noncomputable section

open Filter Topology Asymptotics
open scoped InnerProductSpace


open BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]













variable (T : UnboundedSelfAdjoint H) (S : ℕ → UnboundedSelfAdjoint H)

theorem BookProof.ChapterSirkTrotterKato.trotterKato_tendsto (hres : StrongResolventConvergence T S) (v : H) (t : ℝ) :
    Tendsto (fun n => (S n).stoneU t v) atTop (𝓝 (T.stoneU t v)) := by sorry
