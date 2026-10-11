-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_varScore_eq_zero_iff
-- name    : BookProof.ChapterSoftmaxFluctuation.varScore_eq_zero_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:17:26.748152+00:00
-- url     : https://prove2.me/theorems/e97b481a-58e1-470e-961b-89eb28e4f2af
-- title:
--   `BookProof.ChapterSoftmaxFluctuation.varScore_eq_zero_iff` (beta : ℝ) (s : Fin m → ℝ) : varScore beta s = 0 ↔ ∀ l, s l = meanScore beta s
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxFluctuation`.
--
--   `BookProof.ChapterSoftmaxFluctuation.varScore_eq_zero_iff` (beta : ℝ) (s : Fin m → ℝ) : varScore beta s = 0 ↔ ∀ l, s l = meanScore beta s
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxFluctuation.varScore_eq_zero_iff`.

-- Generated from ChapterSoftmaxFluctuation.lean — theorem BookProof.ChapterSoftmaxFluctuation.varScore_eq_zero_iff
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

theorem BookProof.ChapterSoftmaxFluctuation.varScore_eq_zero_iff (beta : ℝ) (s : Fin m → ℝ) :
    varScore beta s = 0 ↔ ∀ l, s l = meanScore beta s := by sorry
