-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxDivergence_fisherInformation_eq_varScore
-- name    : BookProof.ChapterSoftmaxDivergence.fisherInformation_eq_varScore
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T00:07:38.684079+00:00
-- url     : https://prove2.me/theorems/4b65568c-60f9-473d-9d63-4bd2defdac18
-- title:
--   `BookProof.ChapterSoftmaxDivergence.fisherInformation_eq_varScore` (beta : ℝ) (s : Fin m → ℝ) : fisherInformation beta s = varScore beta s
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxDivergence`.
--
--   `BookProof.ChapterSoftmaxDivergence.fisherInformation_eq_varScore` (beta : ℝ) (s : Fin m → ℝ) : fisherInformation beta s = varScore beta s
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxDivergence.fisherInformation_eq_varScore`.

-- Generated from ChapterSoftmaxDivergence.lean — theorem BookProof.ChapterSoftmaxDivergence.fisherInformation_eq_varScore
import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterSoftmaxDivergence
import Definitions.Def_ChapterSoftmaxFluctuation
open BookProof.ChapterSoftmaxDivergence


open scoped BigOperators

noncomputable section


open BookProof.ChapterAttentionEntropy BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxFluctuation

variable {m : ℕ}

theorem BookProof.ChapterSoftmaxDivergence.fisherInformation_eq_varScore (beta : ℝ) (s : Fin m → ℝ) :
    fisherInformation beta s = varScore beta s := by sorry
