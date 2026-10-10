-- Prove2me | Theorems.Thm_BookProof_ChapterMaxEntropy_isProb_uniform
-- name    : BookProof.ChapterMaxEntropy.isProb_uniform
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T13:01:38.582988+00:00
-- url     : https://prove2.me/theorems/8c8b8cbc-faf1-4338-9f6d-9787a8063050
-- title:
--   `BookProof.ChapterMaxEntropy.isProb_uniform` [Nonempty α] : IsProb (uniform α)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMaxEntropy`.
--
--   `BookProof.ChapterMaxEntropy.isProb_uniform` [Nonempty α] : IsProb (uniform α)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMaxEntropy.isProb_uniform`.

-- Generated from ChapterMaxEntropy.lean — theorem BookProof.ChapterMaxEntropy.isProb_uniform
import Mathlib
import Definitions.Def_ChapterMaxEntropy
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterDutchBook
open BookProof.ChapterA3n
open BookProof.ChapterDutchBook
open BookProof.ChapterMaxEntropy


open Real BigOperators Finset


variable {α : Type*} [Fintype α]

theorem BookProof.ChapterMaxEntropy.isProb_uniform [Nonempty α] : IsProb (uniform α) := by sorry
