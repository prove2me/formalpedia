-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionMixture_le_shannonEntropy_mixture
-- name    : BookProof.ChapterAttentionMixture.le_shannonEntropy_mixture
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:31:41.689724+00:00
-- url     : https://prove2.me/theorems/babafb4a-2343-4d03-a769-ae53bb20a89b
-- title:
--   `BookProof.ChapterAttentionMixture.le_shannonEntropy_mixture` {w : Fin H → ℝ} {p : Fin H → Fin m → ℝ} (hw0 : ∀ h, 0 ≤ w h) (hw : ∑ h, w h = 1) (hp0 : ∀ h j, 0 ≤ p h j) : ∑...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionMixture`.
--
--   `BookProof.ChapterAttentionMixture.le_shannonEntropy_mixture` {w : Fin H → ℝ} {p : Fin H → Fin m → ℝ} (hw0 : ∀ h, 0 ≤ w h) (hw : ∑ h, w h = 1) (hp0 : ∀ h j, 0 ≤ p h j) : ∑ h, w h * shannonEntropy (p h) ≤ shannonEntropy (mixture w p)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionMixture.le_shannonEntropy_mixture`.

-- Generated from ChapterAttentionMixture.lean — theorem BookProof.ChapterAttentionMixture.le_shannonEntropy_mixture
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionMixture
import Definitions.Def_ChapterAttentionEntropy
open BookProof.ChapterAttentionMixture


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterAttentionEntropy

variable {m H : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionMixture.le_shannonEntropy_mixture {w : Fin H → ℝ} {p : Fin H → Fin m → ℝ}
    (hw0 : ∀ h, 0 ≤ w h) (hw : ∑ h, w h = 1) (hp0 : ∀ h j, 0 ≤ p h j) :
    ∑ h, w h * shannonEntropy (p h) ≤ shannonEntropy (mixture w p) := by sorry
