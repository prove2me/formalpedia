-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionRetrieval_card_erase_cast
-- name    : BookProof.ChapterAttentionRetrieval.card_erase_cast
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:42:46.036983+00:00
-- url     : https://prove2.me/theorems/2d56d0aa-15ab-4255-a33c-685a280a0013
-- title:
--   `BookProof.ChapterAttentionRetrieval.card_erase_cast` (j : Fin m) : ((Finset.univ.erase j).card : ℝ) = (m : ℝ) - 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionRetrieval`.
--
--   `BookProof.ChapterAttentionRetrieval.card_erase_cast` (j : Fin m) : ((Finset.univ.erase j).card : ℝ) = (m : ℝ) - 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionRetrieval.card_erase_cast`.

-- Generated from ChapterAttentionRetrieval.lean — theorem BookProof.ChapterAttentionRetrieval.card_erase_cast
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionRetrieval
open BookProof.ChapterAttentionRetrieval


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionRetrieval.card_erase_cast (j : Fin m) :
    ((Finset.univ.erase j).card : ℝ) = (m : ℝ) - 1 := by sorry
