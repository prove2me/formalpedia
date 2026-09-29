-- Prove2me | Theorems.Thm_BookProof_ChapterSirkTrotterKato_trotterKato_uniform_on_interval
-- name    : BookProof.ChapterSirkTrotterKato.trotterKato_uniform_on_interval
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T06:02:58.913045+00:00
-- url     : https://prove2.me/theorems/d31362e2-47c7-49eb-8e7e-622df8816917
-- title:
--   (hres : StrongResolventConvergence T S) (v : H) {T₀ : ℝ} (hT₀ : 0 ≤ T₀) {ε : ℝ} (hε : 0 < ε) : ∀ᶠ n in atTop, ∀ t : ℝ, |t| ≤ T₀ → ‖(S n).stoneU t v - T.stoneU t v‖ ≤ ε
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkTrotterKato.trotterKato_uniform_on_interval` (module `BookProof.ChapterSirkTrotterKato`), source chapter `BookProof/ChapterChapterSirkTrotterKato.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkTrotterKato.lean

-- Generated from ChapterSirkTrotterKato.lean — theorem BookProof.ChapterSirkTrotterKato.trotterKato_uniform_on_interval
import Mathlib
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterSirkTrotterKato










noncomputable section

open Filter Topology Asymptotics
open scoped InnerProductSpace


open BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]













variable (T : UnboundedSelfAdjoint H) (S : ℕ → UnboundedSelfAdjoint H)

theorem BookProof.ChapterSirkTrotterKato.trotterKato_uniform_on_interval (hres : StrongResolventConvergence T S) (v : H)
    {T₀ : ℝ} (hT₀ : 0 ≤ T₀) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ t : ℝ, |t| ≤ T₀ → ‖(S n).stoneU t v - T.stoneU t v‖ ≤ ε := by sorry
