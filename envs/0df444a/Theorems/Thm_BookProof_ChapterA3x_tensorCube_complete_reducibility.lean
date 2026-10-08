-- Prove2me | Theorems.Thm_BookProof_ChapterA3x_tensorCube_complete_reducibility
-- name    : BookProof.ChapterA3x.tensorCube_complete_reducibility
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:40:27.607977+00:00
-- url     : https://prove2.me/theorems/672431b4-56d8-4c26-adcb-1224bef80b8c
-- title:
--   `BookProof.ChapterA3x.tensorCube_complete_reducibility` : projSym 3 + projAnti 3 + projMixed 3 = 1 ∧ projSym 3 * projSym 3 = projSym 3 ∧ projAnti 3 * projAnti 3 = projAnti 3 ∧ proj
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3x`.
--
--   `BookProof.ChapterA3x.tensorCube_complete_reducibility` : projSym 3 + projAnti 3 + projMixed 3 = 1 ∧ projSym 3 * projSym 3 = projSym 3 ∧ projAnti 3 * projAnti 3 = projAnti 3 ∧ projMixed 3 * projMixed 3 = projMixed 3 ∧ projSym 3 * projAnti 3 = 0 ∧ projAnti 3 * projSym 3 = 0 ∧ projSym 3 * projMixed 3 = 0 ∧ projMixed 3 * projSym 3 = 0 ∧ projAnti 3 * projMixed 3 = 0 ∧ projMixed 3 * projAnti 3 = 0 ∧ projMixed 3 ≠ 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3x.tensorCube_complete_reducibility`.

-- Generated from ChapterA3x.lean — theorem BookProof.ChapterA3x.tensorCube_complete_reducibility
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3p
import Mathlib
import Definitions.Def_ChapterA3x
import Definitions.Def_ChapterA3l
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterA3o
open BookProof.ChapterA3l
open BookProof.ChapterA3n
open BookProof.ChapterA3o
open BookProof.ChapterA3x


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o
open BookProof.ChapterA3p

theorem BookProof.ChapterA3x.tensorCube_complete_reducibility :
    projSym 3 + projAnti 3 + projMixed 3 = 1 ∧
    projSym 3 * projSym 3 = projSym 3 ∧
    projAnti 3 * projAnti 3 = projAnti 3 ∧
    projMixed 3 * projMixed 3 = projMixed 3 ∧
    projSym 3 * projAnti 3 = 0 ∧ projAnti 3 * projSym 3 = 0 ∧
    projSym 3 * projMixed 3 = 0 ∧ projMixed 3 * projSym 3 = 0 ∧
    projAnti 3 * projMixed 3 = 0 ∧ projMixed 3 * projAnti 3 = 0 ∧
    projMixed 3 ≠ 0 := by sorry
