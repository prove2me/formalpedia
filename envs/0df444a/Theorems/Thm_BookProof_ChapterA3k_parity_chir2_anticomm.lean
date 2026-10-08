-- Prove2me | Theorems.Thm_BookProof_ChapterA3k_parity_chir2_anticomm
-- name    : BookProof.ChapterA3k.parity_chir2_anticomm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T13:31:18.72667+00:00
-- url     : https://prove2.me/theorems/11b4aab0-d2d0-4a27-9dae-1e8177660136
-- title:
--   `BookProof.ChapterA3k.parity_chir2_anticomm` : parityDiag * chir2 = -(chir2 * parityDiag)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3k`.
--
--   `BookProof.ChapterA3k.parity_chir2_anticomm` : parityDiag * chir2 = -(chir2 * parityDiag)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3k.parity_chir2_anticomm`.

-- Generated from ChapterA3k.lean — theorem BookProof.ChapterA3k.parity_chir2_anticomm
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

theorem BookProof.ChapterA3k.parity_chir2_anticomm : parityDiag * chir2 = -(chir2 * parityDiag) := by sorry
