-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_deriv_meanScore
-- name    : BookProof.ChapterSoftmaxFluctuation.deriv_meanScore
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:16:57.327975+00:00
-- url     : https://prove2.me/theorems/d04519e2-501d-47e0-ab17-3cbc7d67c4ed
-- title:
--   `BookProof.ChapterSoftmaxFluctuation.deriv_meanScore` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : deriv (fun b : ℝ => meanScore b s) beta = varScore beta s
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxFluctuation`.
--
--   `BookProof.ChapterSoftmaxFluctuation.deriv_meanScore` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : deriv (fun b : ℝ => meanScore b s) beta = varScore beta s
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxFluctuation.deriv_meanScore`.

-- Generated from ChapterSoftmaxFluctuation.lean — theorem BookProof.ChapterSoftmaxFluctuation.deriv_meanScore
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterSoftmaxFluctuation
open BookProof.ChapterSoftmaxFluctuation


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterSoftmaxFluctuation.deriv_meanScore (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    deriv (fun b : ℝ => meanScore b s) beta = varScore beta s := by sorry
