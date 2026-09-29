-- Prove2me | Theorems.Thm_BookProof_ChapterH9_krylov_bestApprox_antitone
-- name    : BookProof.ChapterH9.krylov_bestApprox_antitone
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:22:02.928056+00:00
-- url     : https://prove2.me/theorems/2746b9e0-218a-490c-b8bf-21f40ae0f734
-- title:
--   The Lean 4 theorem `krylov_bestApprox_antitone` in the `ChapterH9` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `krylov_bestApprox_antitone` in the `ChapterH9` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH9.lean

-- Generated from ChapterH9.lean — theorem BookProof.ChapterH9.krylov_bestApprox_antitone
import Mathlib
import Definitions.Def_ChapterH9
open BookProof.ChapterH9


noncomputable section


open BookProof.ChapterH1 BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6
open BookProof.ChapterH8
open ContinuousLinearMap


variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem BookProof.ChapterH9.krylov_bestApprox_antitone (H : E →ₗ[ℂ] E) (v : E) {m n : ℕ} (hmn : m ≤ n) (u : E) :
    ‖u - (krylovSpan H v n).starProjection u‖ ≤ ‖u - (krylovSpan H v m).starProjection u‖ := by sorry
