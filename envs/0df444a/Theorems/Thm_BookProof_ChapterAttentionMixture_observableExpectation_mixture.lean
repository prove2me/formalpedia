-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionMixture_observableExpectation_mixture
-- name    : BookProof.ChapterAttentionMixture.observableExpectation_mixture
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:31:24.836903+00:00
-- url     : https://prove2.me/theorems/7170b94b-f87f-4fa0-9208-e78239698a45
-- title:
--   `BookProof.ChapterAttentionMixture.observableExpectation_mixture` (w : Fin H → ℝ) (p : Fin H → Fin m → ℝ) (v : Fin m → E) : observableExpectation (mixture w p) v = ∑ h, w h • obser
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionMixture`.
--
--   `BookProof.ChapterAttentionMixture.observableExpectation_mixture` (w : Fin H → ℝ) (p : Fin H → Fin m → ℝ) (v : Fin m → E) : observableExpectation (mixture w p) v = ∑ h, w h • observableExpectation (p h) v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionMixture.observableExpectation_mixture`.

-- Generated from ChapterAttentionMixture.lean — theorem BookProof.ChapterAttentionMixture.observableExpectation_mixture
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionMixture
import Definitions.Def_ChapterObservableExpectation
open BookProof.ChapterObservableExpectation
open BookProof.ChapterAttentionMixture


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m H : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionMixture.observableExpectation_mixture (w : Fin H → ℝ) (p : Fin H → Fin m → ℝ)
    (v : Fin m → E) :
    observableExpectation (mixture w p) v = ∑ h, w h • observableExpectation (p h) v := by sorry
