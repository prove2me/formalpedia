-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionMixture_mixture_isProb
-- name    : BookProof.ChapterAttentionMixture.mixture_isProb
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:31:18.433013+00:00
-- url     : https://prove2.me/theorems/4bcceb1b-39a3-4482-9115-dc9f48f8b857
-- title:
--   `BookProof.ChapterAttentionMixture.mixture_isProb` {w : Fin H → ℝ} {p : Fin H → Fin m → ℝ} (hw0 : ∀ h, 0 ≤ w h) (hw : ∑ h, w h = 1) (hp0 : ∀ h j, 0 ≤ p h j) (hp : ∀ h, ∑...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionMixture`.
--
--   `BookProof.ChapterAttentionMixture.mixture_isProb` {w : Fin H → ℝ} {p : Fin H → Fin m → ℝ} (hw0 : ∀ h, 0 ≤ w h) (hw : ∑ h, w h = 1) (hp0 : ∀ h j, 0 ≤ p h j) (hp : ∀ h, ∑ j, p h j = 1) : (∀ j, 0 ≤ mixture w p j) ∧ ∑ j, mixture w p j = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionMixture.mixture_isProb`.

-- Generated from ChapterAttentionMixture.lean — theorem BookProof.ChapterAttentionMixture.mixture_isProb
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionMixture
open BookProof.ChapterAttentionMixture


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m H : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionMixture.mixture_isProb {w : Fin H → ℝ} {p : Fin H → Fin m → ℝ} (hw0 : ∀ h, 0 ≤ w h)
    (hw : ∑ h, w h = 1) (hp0 : ∀ h j, 0 ≤ p h j) (hp : ∀ h, ∑ j, p h j = 1) :
    (∀ j, 0 ≤ mixture w p j) ∧ ∑ j, mixture w p j = 1 := by sorry
