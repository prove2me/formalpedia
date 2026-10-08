-- Prove2me | Theorems.Thm_BookProof_ChapterA3n_projSym_parityDiag_comm
-- name    : BookProof.ChapterA3n.projSym_parityDiag_comm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:08:59.087798+00:00
-- url     : https://prove2.me/theorems/2faf3d7c-0c74-49ec-9237-941d21432e86
-- title:
--   `BookProof.ChapterA3n.projSym_parityDiag_comm` {N : ℕ} : projSym N * uniform (mgamma 0) = uniform (mgamma 0) * projSym N
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3n`.
--
--   `BookProof.ChapterA3n.projSym_parityDiag_comm` {N : ℕ} : projSym N * uniform (mgamma 0) = uniform (mgamma 0) * projSym N
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3n.projSym_parityDiag_comm`.

-- Generated from ChapterA3n.lean — theorem BookProof.ChapterA3n.projSym_parityDiag_comm
import Definitions.Def_ChapterA3j
import Mathlib
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3l
open BookProof.ChapterA3
open BookProof.ChapterA3l
open BookProof.ChapterA3n


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j

theorem BookProof.ChapterA3n.projSym_parityDiag_comm {N : ℕ} :
    projSym N * uniform (mgamma 0) = uniform (mgamma 0) * projSym N := by sorry
