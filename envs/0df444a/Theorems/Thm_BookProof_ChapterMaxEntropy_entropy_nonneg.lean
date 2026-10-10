-- Prove2me | Theorems.Thm_BookProof_ChapterMaxEntropy_entropy_nonneg
-- name    : BookProof.ChapterMaxEntropy.entropy_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T13:01:34.795093+00:00
-- url     : https://prove2.me/theorems/aec9b6b6-0e4d-489e-afc9-2f38d3068ead
-- title:
--   `BookProof.ChapterMaxEntropy.entropy_nonneg` {p : α → ℝ} (hp : IsProb p) : 0 ≤ entropy p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMaxEntropy`.
--
--   `BookProof.ChapterMaxEntropy.entropy_nonneg` {p : α → ℝ} (hp : IsProb p) : 0 ≤ entropy p
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMaxEntropy.entropy_nonneg`.

-- Generated from ChapterMaxEntropy.lean — theorem BookProof.ChapterMaxEntropy.entropy_nonneg
import Mathlib
import Definitions.Def_ChapterMaxEntropy
import Definitions.Def_ChapterDutchBook
import Definitions.Def_ChapterIrreversible
open BookProof.ChapterDutchBook
open BookProof.ChapterIrreversible
open BookProof.ChapterMaxEntropy


open Real BigOperators Finset


variable {α : Type*} [Fintype α]

theorem BookProof.ChapterMaxEntropy.entropy_nonneg {p : α → ℝ} (hp : IsProb p) : 0 ≤ entropy p := by sorry
