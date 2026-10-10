-- Prove2me | Theorems.Thm_BookProof_ChapterMaxEntropy_entropy_le_log_card
-- name    : BookProof.ChapterMaxEntropy.entropy_le_log_card
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T13:00:23.176875+00:00
-- url     : https://prove2.me/theorems/8f89b998-7c60-4600-bebf-c6fd390d21f0
-- title:
--   `BookProof.ChapterMaxEntropy.entropy_le_log_card` [Nonempty α] {p : α → ℝ} (hp : IsProb p) : entropy p ≤ Real.log (Fintype.card α)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMaxEntropy`.
--
--   `BookProof.ChapterMaxEntropy.entropy_le_log_card` [Nonempty α] {p : α → ℝ} (hp : IsProb p) : entropy p ≤ Real.log (Fintype.card α)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMaxEntropy.entropy_le_log_card`.

-- Generated from ChapterMaxEntropy.lean — theorem BookProof.ChapterMaxEntropy.entropy_le_log_card
import Mathlib
import Definitions.Def_ChapterMaxEntropy
import Definitions.Def_ChapterDutchBook
import Definitions.Def_ChapterIrreversible
open BookProof.ChapterDutchBook
open BookProof.ChapterIrreversible
open BookProof.ChapterMaxEntropy


open Real BigOperators Finset


variable {α : Type*} [Fintype α]

theorem BookProof.ChapterMaxEntropy.entropy_le_log_card [Nonempty α] {p : α → ℝ} (hp : IsProb p) :
    entropy p ≤ Real.log (Fintype.card α) := by sorry
