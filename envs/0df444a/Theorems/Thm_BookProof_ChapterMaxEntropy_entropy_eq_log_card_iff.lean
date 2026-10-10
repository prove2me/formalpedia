-- Prove2me | Theorems.Thm_BookProof_ChapterMaxEntropy_entropy_eq_log_card_iff
-- name    : BookProof.ChapterMaxEntropy.entropy_eq_log_card_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T13:02:04.228754+00:00
-- url     : https://prove2.me/theorems/8c818172-9ff6-4758-b8d5-d9c3941166a2
-- title:
--   `BookProof.ChapterMaxEntropy.entropy_eq_log_card_iff` [Nonempty α] {p : α → ℝ} (hp : IsProb p) : entropy p = Real.log (Fintype.card α) ↔ p = uniform α
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMaxEntropy`.
--
--   `BookProof.ChapterMaxEntropy.entropy_eq_log_card_iff` [Nonempty α] {p : α → ℝ} (hp : IsProb p) : entropy p = Real.log (Fintype.card α) ↔ p = uniform α
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMaxEntropy.entropy_eq_log_card_iff`.

-- Generated from ChapterMaxEntropy.lean — theorem BookProof.ChapterMaxEntropy.entropy_eq_log_card_iff
import Mathlib
import Definitions.Def_ChapterMaxEntropy
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterDutchBook
import Definitions.Def_ChapterIrreversible
open BookProof.ChapterA3n
open BookProof.ChapterDutchBook
open BookProof.ChapterIrreversible
open BookProof.ChapterMaxEntropy


open Real BigOperators Finset


variable {α : Type*} [Fintype α]

theorem BookProof.ChapterMaxEntropy.entropy_eq_log_card_iff [Nonempty α] {p : α → ℝ} (hp : IsProb p) :
    entropy p = Real.log (Fintype.card α) ↔ p = uniform α := by sorry
