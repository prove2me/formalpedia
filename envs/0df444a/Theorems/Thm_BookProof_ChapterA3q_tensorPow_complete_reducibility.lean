-- Prove2me | Theorems.Thm_BookProof_ChapterA3q_tensorPow_complete_reducibility
-- name    : BookProof.ChapterA3q.tensorPow_complete_reducibility
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:39:45.281987+00:00
-- url     : https://prove2.me/theorems/564115df-e804-4fdc-afaa-97aa7beb1e98
-- title:
--   `BookProof.ChapterA3q.tensorPow_complete_reducibility` {N : ℕ} (hN : 2 ≤ N) : projSym N + projAnti N + projMixed N = 1 ∧ projSym N * projSym N = projSym N ∧ projAnti N * projAnti N
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3q`.
--
--   `BookProof.ChapterA3q.tensorPow_complete_reducibility` {N : ℕ} (hN : 2 ≤ N) : projSym N + projAnti N + projMixed N = 1 ∧ projSym N * projSym N = projSym N ∧ projAnti N * projAnti N = projAnti N ∧ projMixed N * projMixed N = projMixed N ∧ projSym N * projAnti N = 0 ∧ projAnti N * projSym N = 0 ∧ projSym N * projMixed N = 0 ∧ projMixed N * projSym N = 0 ∧ projAnti N * projMixed N = 0 ∧ projMixed N * projAnti N = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3q.tensorPow_complete_reducibility`.

-- Generated from ChapterA3q.lean — theorem BookProof.ChapterA3q.tensorPow_complete_reducibility
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3p
import Mathlib
import Definitions.Def_ChapterA3q
import Definitions.Def_ChapterA3l
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterA3o
open BookProof.ChapterA3l
open BookProof.ChapterA3n
open BookProof.ChapterA3o
open BookProof.ChapterA3q


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o
open BookProof.ChapterA3p

theorem BookProof.ChapterA3q.tensorPow_complete_reducibility {N : ℕ} (hN : 2 ≤ N) :
    projSym N + projAnti N + projMixed N = 1 ∧
    projSym N * projSym N = projSym N ∧
    projAnti N * projAnti N = projAnti N ∧
    projMixed N * projMixed N = projMixed N ∧
    projSym N * projAnti N = 0 ∧ projAnti N * projSym N = 0 ∧
    projSym N * projMixed N = 0 ∧ projMixed N * projSym N = 0 ∧
    projAnti N * projMixed N = 0 ∧ projMixed N * projAnti N = 0 := by sorry
