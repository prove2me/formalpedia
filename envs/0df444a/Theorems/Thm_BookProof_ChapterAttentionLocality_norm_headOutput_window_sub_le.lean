-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionLocality_norm_headOutput_window_sub_le
-- name    : BookProof.ChapterAttentionLocality.norm_headOutput_window_sub_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T09:47:53.298246+00:00
-- url     : https://prove2.me/theorems/656e9d0e-238d-4890-85c5-3f71e0f64a8d
-- title:
--   `BookProof.ChapterAttentionLocality.norm_headOutput_window_sub_le` {beta gamma Delta R : ℝ} (hb : 0 ≤ beta) (hg : 0 ≤ gamma) (s : Fin m → ℝ) (d : Fin m → ℝ) {j₀ : Fin m} (hd0 : d j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionLocality`.
--
--   `BookProof.ChapterAttentionLocality.norm_headOutput_window_sub_le` {beta gamma Delta R : ℝ} (hb : 0 ≤ beta) (hg : 0 ≤ gamma) (s : Fin m → ℝ) (d : Fin m → ℝ) {j₀ : Fin m} (hd0 : d j₀ = 0) (hR : 0 < R) (hDelta : ∀ l, s l ≤ s j₀ + Delta) {v : Fin m → E} {C : ℝ} (hv : ∀ j, ‖v j‖ ≤ C) (hC : 0 ≤ C) : ‖observableExpectation (maskedSoftmax beta (alibiScore s gamma d) (window d R)) v - headOutput beta (alibiScore s gamma d) v‖ ≤ 2 * ((m : ℝ) * (Real.exp (beta * Delta) * Real.exp (-(beta * (gamma * R))))) * C
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionLocality.norm_headOutput_window_sub_le`.

-- Generated from ChapterAttentionLocality.lean — theorem BookProof.ChapterAttentionLocality.norm_headOutput_window_sub_le
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionLocality
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterAttentionMasking
import Definitions.Def_ChapterAttentionOutput
open BookProof.ChapterObservableExpectation
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionLocality


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterAttentionMasking
open BookProof.ChapterAttentionOutput

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionLocality.norm_headOutput_window_sub_le {beta gamma Delta R : ℝ} (hb : 0 ≤ beta)
    (hg : 0 ≤ gamma) (s : Fin m → ℝ) (d : Fin m → ℝ) {j₀ : Fin m} (hd0 : d j₀ = 0)
    (hR : 0 < R) (hDelta : ∀ l, s l ≤ s j₀ + Delta) {v : Fin m → E} {C : ℝ}
    (hv : ∀ j, ‖v j‖ ≤ C) (hC : 0 ≤ C) :
    ‖observableExpectation
        (maskedSoftmax beta (alibiScore s gamma d) (window d R)) v
      - headOutput beta (alibiScore s gamma d) v‖
      ≤ 2 * ((m : ℝ) * (Real.exp (beta * Delta) * Real.exp (-(beta * (gamma * R))))) * C := by sorry
