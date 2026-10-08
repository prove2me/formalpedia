-- Prove2me | Theorems.Thm_BookProof_ChapterEntropyTemperature_attentionEntropy_eq
-- name    : BookProof.ChapterEntropyTemperature.attentionEntropy_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T02:48:58.932018+00:00
-- url     : https://prove2.me/theorems/9e8cff0f-8df8-4dfb-9e2a-ae59052033ce
-- title:
--   `BookProof.ChapterEntropyTemperature.attentionEntropy_eq` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : attentionEntropy beta s = logPartition beta s - beta * meanScore beta s
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEntropyTemperature`.
--
--   `BookProof.ChapterEntropyTemperature.attentionEntropy_eq` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : attentionEntropy beta s = logPartition beta s - beta * meanScore beta s
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEntropyTemperature.attentionEntropy_eq`.

-- Generated from ChapterEntropyTemperature.lean — theorem BookProof.ChapterEntropyTemperature.attentionEntropy_eq
import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterEntropyTemperature
import Definitions.Def_ChapterSoftmaxFluctuation
open BookProof.ChapterEntropyTemperature


open scoped BigOperators

noncomputable section


open BookProof.ChapterAttentionEntropy BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxFluctuation

variable {m : ℕ}

theorem BookProof.ChapterEntropyTemperature.attentionEntropy_eq (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    attentionEntropy beta s = logPartition beta s - beta * meanScore beta s := by sorry
