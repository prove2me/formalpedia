-- Prove2me | Theorems.Thm_BookProof_ChapterA3k_parity_chir1_anticomm
-- name    : BookProof.ChapterA3k.parity_chir1_anticomm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T13:30:45.918989+00:00
-- url     : https://prove2.me/theorems/78a7e735-560f-4fe9-b895-84f65e6d0057
-- title:
--   `BookProof.ChapterA3k.parity_chir1_anticomm` : parityDiag * chir1 = -(chir1 * parityDiag)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3k`.
--
--   `BookProof.ChapterA3k.parity_chir1_anticomm` : parityDiag * chir1 = -(chir1 * parityDiag)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3k.parity_chir1_anticomm`.

-- Generated from ChapterA3k.lean — theorem BookProof.ChapterA3k.parity_chir1_anticomm
import Mathlib
import Definitions.Def_ChapterA3k
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
open BookProof.ChapterA3
open BookProof.ChapterA3j
open BookProof.ChapterA3k


open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j

theorem BookProof.ChapterA3k.parity_chir1_anticomm : parityDiag * chir1 = -(chir1 * parityDiag) := by sorry
