-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionMixture_le_negMulLog_mixture
-- name    : BookProof.ChapterAttentionMixture.le_negMulLog_mixture
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:31:54.019275+00:00
-- url     : https://prove2.me/theorems/1ee181ce-e25a-460f-9ed2-06a13572b752
-- title:
--   `BookProof.ChapterAttentionMixture.le_negMulLog_mixture` {w : Fin H → ℝ} {p : Fin H → Fin m → ℝ} (hw0 : ∀ h, 0 ≤ w h) (hw : ∑ h, w h = 1) (hp0 : ∀ h j, 0 ≤ p h j) (j : Fin m)...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionMixture`.
--
--   `BookProof.ChapterAttentionMixture.le_negMulLog_mixture` {w : Fin H → ℝ} {p : Fin H → Fin m → ℝ} (hw0 : ∀ h, 0 ≤ w h) (hw : ∑ h, w h = 1) (hp0 : ∀ h j, 0 ≤ p h j) (j : Fin m) : ∑ h, w h * Real.negMulLog (p h j) ≤ Real.negMulLog (mixture w p j)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionMixture.le_negMulLog_mixture`.

-- Generated from ChapterAttentionMixture.lean — theorem BookProof.ChapterAttentionMixture.le_negMulLog_mixture
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionMixture
open BookProof.ChapterAttentionMixture


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m H : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionMixture.le_negMulLog_mixture {w : Fin H → ℝ} {p : Fin H → Fin m → ℝ} (hw0 : ∀ h, 0 ≤ w h)
    (hw : ∑ h, w h = 1) (hp0 : ∀ h j, 0 ≤ p h j) (j : Fin m) :
    ∑ h, w h * Real.negMulLog (p h j) ≤ Real.negMulLog (mixture w p j) := by sorry
