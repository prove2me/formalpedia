-- Prove2me | Theorems.Thm_BookProof_ChapterMaxEntropy_IsProb_le_one
-- name    : BookProof.ChapterMaxEntropy.IsProb.le_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:59:52.086571+00:00
-- url     : https://prove2.me/theorems/0c3599a3-6153-49a3-8a2f-005a335525db
-- title:
--   `BookProof.ChapterMaxEntropy.IsProb.le_one` {p : α → ℝ} (hp : IsProb p) (i : α) : p i ≤ 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMaxEntropy`.
--
--   `BookProof.ChapterMaxEntropy.IsProb.le_one` {p : α → ℝ} (hp : IsProb p) (i : α) : p i ≤ 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMaxEntropy.IsProb.le_one`.

-- Generated from ChapterMaxEntropy.lean — theorem BookProof.ChapterMaxEntropy.IsProb.le_one
import Mathlib
import Definitions.Def_ChapterMaxEntropy
import Definitions.Def_ChapterDutchBook
open BookProof.ChapterDutchBook
open BookProof.ChapterMaxEntropy


open Real BigOperators Finset


variable {α : Type*} [Fintype α]

theorem BookProof.ChapterMaxEntropy.IsProb.le_one {p : α → ℝ} (hp : IsProb p) (i : α) : p i ≤ 1 := by sorry
