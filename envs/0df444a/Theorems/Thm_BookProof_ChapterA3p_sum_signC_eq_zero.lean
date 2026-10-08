-- Prove2me | Theorems.Thm_BookProof_ChapterA3p_sum_signC_eq_zero
-- name    : BookProof.ChapterA3p.sum_signC_eq_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T00:35:02.814992+00:00
-- url     : https://prove2.me/theorems/2ab34abe-5ff2-4ef7-a99d-b83541964638
-- title:
--   `BookProof.ChapterA3p.sum_signC_eq_zero` {N : ℕ} (hN : 2 ≤ N) : ∑ σ : Equiv.Perm (Fin N), signC σ = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3p`.
--
--   `BookProof.ChapterA3p.sum_signC_eq_zero` {N : ℕ} (hN : 2 ≤ N) : ∑ σ : Equiv.Perm (Fin N), signC σ = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3p.sum_signC_eq_zero`.

-- Generated from ChapterA3p.lean — theorem BookProof.ChapterA3p.sum_signC_eq_zero
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3n
import Mathlib
import Definitions.Def_ChapterA3p
import Definitions.Def_ChapterA3o
open BookProof.ChapterA3o
open BookProof.ChapterA3p


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o

theorem BookProof.ChapterA3p.sum_signC_eq_zero {N : ℕ} (hN : 2 ≤ N) :
    ∑ σ : Equiv.Perm (Fin N), signC σ = 0 := by sorry
