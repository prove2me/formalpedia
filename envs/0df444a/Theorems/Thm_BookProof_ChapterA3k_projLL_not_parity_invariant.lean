-- Prove2me | Theorems.Thm_BookProof_ChapterA3k_projLL_not_parity_invariant
-- name    : BookProof.ChapterA3k.projLL_not_parity_invariant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T14:11:29.563244+00:00
-- url     : https://prove2.me/theorems/18b25c71-cef1-45db-9a1d-b7ed3fb46748
-- title:
--   `BookProof.ChapterA3k.projLL_not_parity_invariant` : parityDiag * projLL ≠ projLL * parityDiag
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3k`.
--
--   `BookProof.ChapterA3k.projLL_not_parity_invariant` : parityDiag * projLL ≠ projLL * parityDiag
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3k.projLL_not_parity_invariant`.

-- Generated from ChapterA3k.lean — theorem BookProof.ChapterA3k.projLL_not_parity_invariant
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Mathlib
import Definitions.Def_ChapterA3k
open BookProof.ChapterA3k


open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j

theorem BookProof.ChapterA3k.projLL_not_parity_invariant :
    parityDiag * projLL ≠ projLL * parityDiag := by sorry
