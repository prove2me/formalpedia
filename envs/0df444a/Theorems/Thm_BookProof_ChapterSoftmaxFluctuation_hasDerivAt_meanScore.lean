-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_hasDerivAt_meanScore
-- name    : BookProof.ChapterSoftmaxFluctuation.hasDerivAt_meanScore
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:16:53.017035+00:00
-- url     : https://prove2.me/theorems/7014d32c-47c7-422a-ab83-1949db942ae5
-- title:
--   `BookProof.ChapterSoftmaxFluctuation.hasDerivAt_meanScore` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : HasDerivAt (fun b : ℝ => meanScore b s) (varScore beta s) beta
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxFluctuation`.
--
--   `BookProof.ChapterSoftmaxFluctuation.hasDerivAt_meanScore` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : HasDerivAt (fun b : ℝ => meanScore b s) (varScore beta s) beta
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxFluctuation.hasDerivAt_meanScore`.

-- Generated from ChapterSoftmaxFluctuation.lean — theorem BookProof.ChapterSoftmaxFluctuation.hasDerivAt_meanScore
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

theorem BookProof.ChapterSoftmaxFluctuation.hasDerivAt_meanScore (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    HasDerivAt (fun b : ℝ => meanScore b s) (varScore beta s) beta := by sorry
