-- Prove2me | Theorems.Thm_BookProof_ChapterMaxEntropy_entropy_le_entropy_uniform
-- name    : BookProof.ChapterMaxEntropy.entropy_le_entropy_uniform
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T13:00:53.182148+00:00
-- url     : https://prove2.me/theorems/e5b523b9-36f1-4c21-9f69-a205f2f5cb7a
-- title:
--   `BookProof.ChapterMaxEntropy.entropy_le_entropy_uniform` [Nonempty α] {p : α → ℝ} (hp : IsProb p) : entropy p ≤ entropy (uniform α)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMaxEntropy`.
--
--   `BookProof.ChapterMaxEntropy.entropy_le_entropy_uniform` [Nonempty α] {p : α → ℝ} (hp : IsProb p) : entropy p ≤ entropy (uniform α)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMaxEntropy.entropy_le_entropy_uniform`.

-- Generated from ChapterMaxEntropy.lean — theorem BookProof.ChapterMaxEntropy.entropy_le_entropy_uniform
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

theorem BookProof.ChapterMaxEntropy.entropy_le_entropy_uniform [Nonempty α] {p : α → ℝ} (hp : IsProb p) :
    entropy p ≤ entropy (uniform α) := by sorry
