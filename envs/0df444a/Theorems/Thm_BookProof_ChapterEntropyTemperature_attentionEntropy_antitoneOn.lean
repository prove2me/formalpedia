-- Prove2me | Theorems.Thm_BookProof_ChapterEntropyTemperature_attentionEntropy_antitoneOn
-- name    : BookProof.ChapterEntropyTemperature.attentionEntropy_antitoneOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T02:50:34.965346+00:00
-- url     : https://prove2.me/theorems/4f00d864-8114-4672-b082-28e598bcca03
-- title:
--   `BookProof.ChapterEntropyTemperature.attentionEntropy_antitoneOn` (s : Fin m → ℝ) (i : Fin m) : AntitoneOn (fun b : ℝ => attentionEntropy b s) (Set.Ici (0 : ℝ))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEntropyTemperature`.
--
--   `BookProof.ChapterEntropyTemperature.attentionEntropy_antitoneOn` (s : Fin m → ℝ) (i : Fin m) : AntitoneOn (fun b : ℝ => attentionEntropy b s) (Set.Ici (0 : ℝ))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEntropyTemperature.attentionEntropy_antitoneOn`.

-- Generated from ChapterEntropyTemperature.lean — theorem BookProof.ChapterEntropyTemperature.attentionEntropy_antitoneOn
import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterEntropyTemperature
open BookProof.ChapterEntropyTemperature


open scoped BigOperators

noncomputable section


open BookProof.ChapterAttentionEntropy BookProof.ChapterSoftmaxSharpness

variable {m : ℕ}

theorem BookProof.ChapterEntropyTemperature.attentionEntropy_antitoneOn (s : Fin m → ℝ) (i : Fin m) :
    AntitoneOn (fun b : ℝ => attentionEntropy b s) (Set.Ici (0 : ℝ)) := by sorry
