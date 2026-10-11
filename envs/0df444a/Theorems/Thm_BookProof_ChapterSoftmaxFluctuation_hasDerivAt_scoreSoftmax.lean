-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_hasDerivAt_scoreSoftmax
-- name    : BookProof.ChapterSoftmaxFluctuation.hasDerivAt_scoreSoftmax
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:16:37.142762+00:00
-- url     : https://prove2.me/theorems/b38afee5-054d-402e-b560-f3fe402d2716
-- title:
--   `BookProof.ChapterSoftmaxFluctuation.hasDerivAt_scoreSoftmax` (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) : HasDerivAt (fun b : ℝ => scoreSoftmax b s j) (scoreSoftmax beta s j * (s j -
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxFluctuation`.
--
--   `BookProof.ChapterSoftmaxFluctuation.hasDerivAt_scoreSoftmax` (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) : HasDerivAt (fun b : ℝ => scoreSoftmax b s j) (scoreSoftmax beta s j * (s j - meanScore beta s)) beta
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxFluctuation.hasDerivAt_scoreSoftmax`.

-- Generated from ChapterSoftmaxFluctuation.lean — theorem BookProof.ChapterSoftmaxFluctuation.hasDerivAt_scoreSoftmax
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterSoftmaxFluctuation
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxFluctuation


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterSoftmaxFluctuation.hasDerivAt_scoreSoftmax (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    HasDerivAt (fun b : ℝ => scoreSoftmax b s j)
      (scoreSoftmax beta s j * (s j - meanScore beta s)) beta := by sorry
