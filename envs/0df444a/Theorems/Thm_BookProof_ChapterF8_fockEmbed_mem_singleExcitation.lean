-- Prove2me | Theorems.Thm_BookProof_ChapterF8_fockEmbed_mem_singleExcitation
-- name    : BookProof.ChapterF8.fockEmbed_mem_singleExcitation
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T05:07:55.682451+00:00
-- url     : https://prove2.me/theorems/ebc992ca-3b7e-4bc5-aeb1-4f58cdb19553
-- title:
--   `BookProof.ChapterF8.fockEmbed_mem_singleExcitation` {k K : ℕ} (g : Fin k → Fin K) (y : Fin k → ℝ) : fockEmbed g y ∈ singleExcitation K
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF8`.
--
--   `BookProof.ChapterF8.fockEmbed_mem_singleExcitation` {k K : ℕ} (g : Fin k → Fin K) (y : Fin k → ℝ) : fockEmbed g y ∈ singleExcitation K
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF8.fockEmbed_mem_singleExcitation`.

-- Generated from ChapterF8.lean — theorem BookProof.ChapterF8.fockEmbed_mem_singleExcitation
import Mathlib
import Definitions.Def_ChapterF8
import Definitions.Def_ChapterNavierStokesFockManyMode
open BookProof.NavierStokesFlow.FockManyMode
open BookProof.ChapterF8


noncomputable section

open scoped BigOperators

theorem BookProof.ChapterF8.fockEmbed_mem_singleExcitation {k K : ℕ} (g : Fin k → Fin K) (y : Fin k → ℝ) :
    fockEmbed g y ∈ singleExcitation K := by sorry
