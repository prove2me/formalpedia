-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionMixture_mixture_sum_one
-- name    : BookProof.ChapterAttentionMixture.mixture_sum_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:31:16.550476+00:00
-- url     : https://prove2.me/theorems/d0190ecc-8cfa-40d9-b5e0-08be82da6180
-- title:
--   `BookProof.ChapterAttentionMixture.mixture_sum_one` {w : Fin H → ℝ} {p : Fin H → Fin m → ℝ} (hw : ∑ h, w h = 1) (hp : ∀ h, ∑ j, p h j = 1) : ∑ j, mixture w p j = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionMixture`.
--
--   `BookProof.ChapterAttentionMixture.mixture_sum_one` {w : Fin H → ℝ} {p : Fin H → Fin m → ℝ} (hw : ∑ h, w h = 1) (hp : ∀ h, ∑ j, p h j = 1) : ∑ j, mixture w p j = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionMixture.mixture_sum_one`.

-- Generated from ChapterAttentionMixture.lean — theorem BookProof.ChapterAttentionMixture.mixture_sum_one
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionMixture
open BookProof.ChapterAttentionMixture


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m H : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionMixture.mixture_sum_one {w : Fin H → ℝ} {p : Fin H → Fin m → ℝ} (hw : ∑ h, w h = 1)
    (hp : ∀ h, ∑ j, p h j = 1) : ∑ j, mixture w p j = 1 := by sorry
