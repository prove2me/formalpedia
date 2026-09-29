-- Prove2me | Theorems.Thm_BookProof_ChapterSirkTrotterKato_trotterKato_uniform_of_mem_range
-- name    : BookProof.ChapterSirkTrotterKato.trotterKato_uniform_of_mem_range
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:13:47.863993+00:00
-- url     : https://prove2.me/theorems/cb47c37a-a052-4ba4-b4d3-47c2960ecd03
-- title:
--   (hres : StrongResolventConvergence T S) (w : T.domain) {T₀ : ℝ} (hT₀ : 0 ≤ T₀) {ε : ℝ} (hε : 0 < ε) : ∀ᶠ n in atTop, ∀ t : ℝ, |t| ≤ T₀ → ‖(S n).stoneU t (T.resCLM 1...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkTrotterKato.trotterKato_uniform_of_mem_range` (module `BookProof.ChapterSirkTrotterKato`), source chapter `BookProof/ChapterChapterSirkTrotterKato.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkTrotterKato.lean

-- Generated from ChapterSirkTrotterKato.lean — theorem BookProof.ChapterSirkTrotterKato.trotterKato_uniform_of_mem_range
import Mathlib
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterSirkTrotterKato










noncomputable section

open Filter Topology Asymptotics
open scoped InnerProductSpace


open BookProof.ChapterStoneResolvent
open BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]













variable (T : UnboundedSelfAdjoint H) (S : ℕ → UnboundedSelfAdjoint H)

theorem BookProof.ChapterSirkTrotterKato.trotterKato_uniform_of_mem_range (hres : StrongResolventConvergence T S)
    (w : T.domain) {T₀ : ℝ} (hT₀ : 0 ≤ T₀) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ t : ℝ, |t| ≤ T₀ →
      ‖(S n).stoneU t (T.resCLM 1 (w : H)) - T.stoneU t (T.resCLM 1 (w : H))‖ ≤ ε := by sorry
