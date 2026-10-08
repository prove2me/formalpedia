-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionLocality_mem_window
-- name    : BookProof.ChapterAttentionLocality.mem_window
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:26:46.144416+00:00
-- url     : https://prove2.me/theorems/ade707f8-69ca-4486-b579-1913505ebd10
-- title:
--   `BookProof.ChapterAttentionLocality.mem_window` {d : Fin m → ℝ} {R : ℝ} {l : Fin m} : l ∈ window d R ↔ d l < R
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionLocality`.
--
--   `BookProof.ChapterAttentionLocality.mem_window` {d : Fin m → ℝ} {R : ℝ} {l : Fin m} : l ∈ window d R ↔ d l < R
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionLocality.mem_window`.

-- Generated from ChapterAttentionLocality.lean — theorem BookProof.ChapterAttentionLocality.mem_window
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionLocality
open BookProof.ChapterAttentionLocality


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionLocality.mem_window {d : Fin m → ℝ} {R : ℝ} {l : Fin m} : l ∈ window d R ↔ d l < R := by sorry
