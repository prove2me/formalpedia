-- Prove2me | Theorems.Thm_BookProof_ChapterSirkTrotterKato_tendsto_uniformly_on_isCompact_of_tendsto
-- name    : BookProof.ChapterSirkTrotterKato.tendsto_uniformly_on_isCompact_of_tendsto
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:52:16.524736+00:00
-- url     : https://prove2.me/theorems/1df6a896-56b4-452f-bf11-8f3b85c633e8
-- title:
--   {D : ℕ → H →L[ℂ] H} {M : ℝ} (hM : ∀ n y, ‖D n y‖ ≤ M * ‖y‖) (hptw : ∀ y, Tendsto (fun n => D n y) atTop (𝓝 0)) {K : Set H} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε)...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkTrotterKato.tendsto_uniformly_on_isCompact_of_tendsto` (module `BookProof.ChapterSirkTrotterKato`), source chapter `BookProof/ChapterChapterSirkTrotterKato.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkTrotterKato.lean

-- Generated from ChapterSirkTrotterKato.lean — theorem BookProof.ChapterSirkTrotterKato.tendsto_uniformly_on_isCompact_of_tendsto
import Mathlib
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterSirkTrotterKato










noncomputable section

open Filter Topology Asymptotics
open scoped InnerProductSpace


open BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem BookProof.ChapterSirkTrotterKato.tendsto_uniformly_on_isCompact_of_tendsto {D : ℕ → H →L[ℂ] H} {M : ℝ}
    (hM : ∀ n y, ‖D n y‖ ≤ M * ‖y‖) (hptw : ∀ y, Tendsto (fun n => D n y) atTop (𝓝 0))
    {K : Set H} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ y ∈ K, ‖D n y‖ ≤ ε := by sorry
