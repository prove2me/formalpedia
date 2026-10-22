-- Prove2me | Theorems.Thm_BookProof_ChapterF3_diagonal_gram_residual_orthogonal
-- name    : BookProof.ChapterF3.diagonal_gram_residual_orthogonal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T15:08:09.342337+00:00
-- url     : https://prove2.me/theorems/45d7bc33-0057-45e0-9261-31d64619bcea
-- title:
--   `BookProof.ChapterF3.diagonal_gram_residual_orthogonal` {ι : Type*} [Fintype ι] (g : ι → E) (b : E) (horth : ∀ i j, i ≠ j → inner (𝕜
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF3`.
--
--   `BookProof.ChapterF3.diagonal_gram_residual_orthogonal` {ι : Type*} [Fintype ι] (g : ι → E) (b : E) (horth : ∀ i j, i ≠ j → inner (𝕜
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF3.diagonal_gram_residual_orthogonal`.

-- Generated from ChapterF3.lean —
import Mathlib
import Definitions.Def_ChapterF3
import Definitions.Def_ChapterGhostField
open BookProof.GhostField
open BookProof.ChapterF3


open scoped BigOperators
open Polynomial


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterF3.diagonal_gram_residual_orthogonal {ι : Type*} [Fintype ι]
    (g : ι → E) (b : E)
    (horth : ∀ i j, i ≠ j → inner (𝕜 := ℂ) (g i) (g j) = 0)
    (hne : ∀ i, g i ≠ 0) (k : ι) :
    inner (𝕜 := ℂ) (g k)
      (b - ∑ j, ((inner (𝕜 := ℂ) (g j) b) / ((‖g j‖ : ℂ) ^ 2)) • g j) = 0 := by sorry
