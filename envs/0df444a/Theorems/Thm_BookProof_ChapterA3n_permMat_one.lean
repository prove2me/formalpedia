-- Prove2me | Theorems.Thm_BookProof_ChapterA3n_permMat_one
-- name    : BookProof.ChapterA3n.permMat_one
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:07:28.35533+00:00
-- url     : https://prove2.me/theorems/1976d153-c640-462f-aaea-80cfc9a66448
-- title:
--   `BookProof.ChapterA3n.permMat_one` {N : ℕ} : permMat (1 : Equiv.Perm (Fin N)) = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3n`.
--
--   `BookProof.ChapterA3n.permMat_one` {N : ℕ} : permMat (1 : Equiv.Perm (Fin N)) = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3n.permMat_one`.

-- Generated from ChapterA3n.lean — theorem BookProof.ChapterA3n.permMat_one
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Mathlib
import Definitions.Def_ChapterA3n
open BookProof.ChapterA3n


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j

theorem BookProof.ChapterA3n.permMat_one {N : ℕ} : permMat (1 : Equiv.Perm (Fin N)) = 1 := by sorry
