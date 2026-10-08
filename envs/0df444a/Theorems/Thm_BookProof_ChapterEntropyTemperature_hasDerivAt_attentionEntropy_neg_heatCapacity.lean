-- Prove2me | Theorems.Thm_BookProof_ChapterEntropyTemperature_hasDerivAt_attentionEntropy_neg_heatCapacity
-- name    : BookProof.ChapterEntropyTemperature.hasDerivAt_attentionEntropy_neg_heatCapacity
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T02:49:26.272311+00:00
-- url     : https://prove2.me/theorems/5292d695-2268-4747-be4e-74febef1ea27
-- title:
--   `BookProof.ChapterEntropyTemperature.hasDerivAt_attentionEntropy_neg_heatCapacity` {beta : ℝ} (hbeta : beta ≠ 0) (s : Fin m → ℝ) (i : Fin m) : HasDerivAt (fun b : ℝ => attentionEnt
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEntropyTemperature`.
--
--   `BookProof.ChapterEntropyTemperature.hasDerivAt_attentionEntropy_neg_heatCapacity` {beta : ℝ} (hbeta : beta ≠ 0) (s : Fin m → ℝ) (i : Fin m) : HasDerivAt (fun b : ℝ => attentionEntropy b s) (-(heatCapacity beta s / beta)) beta
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEntropyTemperature.hasDerivAt_attentionEntropy_neg_heatCapacity`.

-- Generated from ChapterEntropyTemperature.lean — theorem BookProof.ChapterEntropyTemperature.hasDerivAt_attentionEntropy_neg_heatCapacity
import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterEntropyTemperature
open BookProof.ChapterEntropyTemperature


open scoped BigOperators

noncomputable section


open BookProof.ChapterAttentionEntropy BookProof.ChapterSoftmaxSharpness

variable {m : ℕ}

theorem BookProof.ChapterEntropyTemperature.hasDerivAt_attentionEntropy_neg_heatCapacity {beta : ℝ} (hbeta : beta ≠ 0)
    (s : Fin m → ℝ) (i : Fin m) :
    HasDerivAt (fun b : ℝ => attentionEntropy b s) (-(heatCapacity beta s / beta)) beta := by sorry
