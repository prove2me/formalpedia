-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionStreaming_snoc_denom
-- name    : BookProof.ChapterAttentionStreaming.snoc_denom
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:49:44.205796+00:00
-- url     : https://prove2.me/theorems/6d32411a-61eb-4e5b-9b60-038917060513
-- title:
--   `BookProof.ChapterAttentionStreaming.snoc_denom` (beta sn : ℝ) (s : Fin m → ℝ) : ∑ l, Real.exp (beta * (Fin.snoc s sn : Fin (m + 1) → ℝ) l) = (∑ l, Real.exp (beta * s l)) + Real.ex
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionStreaming`.
--
--   `BookProof.ChapterAttentionStreaming.snoc_denom` (beta sn : ℝ) (s : Fin m → ℝ) : ∑ l, Real.exp (beta * (Fin.snoc s sn : Fin (m + 1) → ℝ) l) = (∑ l, Real.exp (beta * s l)) + Real.exp (beta * sn)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionStreaming.snoc_denom`.

-- Generated from ChapterAttentionStreaming.lean — theorem BookProof.ChapterAttentionStreaming.snoc_denom
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionStreaming
open BookProof.ChapterAttentionStreaming


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionStreaming.snoc_denom (beta sn : ℝ) (s : Fin m → ℝ) :
    ∑ l, Real.exp (beta * (Fin.snoc s sn : Fin (m + 1) → ℝ) l)
      = (∑ l, Real.exp (beta * s l)) + Real.exp (beta * sn) := by sorry
