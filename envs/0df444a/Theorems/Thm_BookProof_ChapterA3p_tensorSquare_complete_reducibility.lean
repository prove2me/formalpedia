-- Prove2me | Theorems.Thm_BookProof_ChapterA3p_tensorSquare_complete_reducibility
-- name    : BookProof.ChapterA3p.tensorSquare_complete_reducibility
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T00:35:51.507406+00:00
-- url     : https://prove2.me/theorems/866139e8-dbbd-4474-96d0-4e2764abff10
-- title:
--   `BookProof.ChapterA3p.tensorSquare_complete_reducibility` : projSym 2 + projAnti 2 = 1 ∧ projSym 2 * projAnti 2 = 0 ∧ projAnti 2 * projSym 2 = 0 ∧ projSym 2 * projSym 2 = projSym 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3p`.
--
--   `BookProof.ChapterA3p.tensorSquare_complete_reducibility` : projSym 2 + projAnti 2 = 1 ∧ projSym 2 * projAnti 2 = 0 ∧ projAnti 2 * projSym 2 = 0 ∧ projSym 2 * projSym 2 = projSym 2 ∧ projAnti 2 * projAnti 2 = projAnti 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3p.tensorSquare_complete_reducibility`.

-- Generated from ChapterA3p.lean — theorem BookProof.ChapterA3p.tensorSquare_complete_reducibility
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Mathlib
import Definitions.Def_ChapterA3p
import Definitions.Def_ChapterA3l
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterA3o
open BookProof.ChapterA3l
open BookProof.ChapterA3n
open BookProof.ChapterA3o
open BookProof.ChapterA3p


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o

theorem BookProof.ChapterA3p.tensorSquare_complete_reducibility :
    projSym 2 + projAnti 2 = 1 ∧
    projSym 2 * projAnti 2 = 0 ∧
    projAnti 2 * projSym 2 = 0 ∧
    projSym 2 * projSym 2 = projSym 2 ∧
    projAnti 2 * projAnti 2 = projAnti 2 := by sorry
