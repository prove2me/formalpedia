-- Prove2me | Theorems.Thm_BookProof_ChapterMaxEntropy_entropy_uniform
-- name    : BookProof.ChapterMaxEntropy.entropy_uniform
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T13:00:52.337404+00:00
-- url     : https://prove2.me/theorems/bef3c13c-e97b-42e4-b55b-0c4c794d0df9
-- title:
--   `BookProof.ChapterMaxEntropy.entropy_uniform` [Nonempty α] : entropy (uniform α) = Real.log (Fintype.card α)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMaxEntropy`.
--
--   `BookProof.ChapterMaxEntropy.entropy_uniform` [Nonempty α] : entropy (uniform α) = Real.log (Fintype.card α)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMaxEntropy.entropy_uniform`.

-- Generated from ChapterMaxEntropy.lean — theorem BookProof.ChapterMaxEntropy.entropy_uniform
import Mathlib
import Definitions.Def_ChapterMaxEntropy
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterIrreversible
open BookProof.ChapterA3n
open BookProof.ChapterIrreversible
open BookProof.ChapterMaxEntropy


open Real BigOperators Finset


variable {α : Type*} [Fintype α]

theorem BookProof.ChapterMaxEntropy.entropy_uniform [Nonempty α] :
    entropy (uniform α) = Real.log (Fintype.card α) := by sorry
