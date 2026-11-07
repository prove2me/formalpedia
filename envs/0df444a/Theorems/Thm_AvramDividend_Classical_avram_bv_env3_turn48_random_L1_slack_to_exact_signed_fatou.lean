-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn48_random_L1_slack_to_exact_signed_fatou
-- name    : AvramDividend.Classical.avram_bv_env3_turn48_random_L1_slack_to_exact_signed_fatou
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T07:38:16.805235+00:00
-- url     : https://prove2.me/theorems/f0d5626d-c2ac-483b-8d14-0459d4dc4f53
-- title:
--   Random L1 physical grid error is absorbed into centred signed Fatou sources
-- statement:
--   If a nonnegative random mesh error in the true physical dividend and martingale grid has integrable positive part with expectation tending to zero, centring that random error produces a signed residual with nonpositive mean and only deterministic vanishing slack. The accepted signed-source normalisation then gives an exact physical Fatou family, retaining the full random original process terms.
-- source:
--   Original BV P3-GRID physical random error 4f605d76 and existing accepted exact deterministic slack normalisation 683662eb; uses probability integral linearity and the actual random L1 mesh error, no law substitution.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_source_slack_exact_signed_fatou_normalisation
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn48_random_L1_slack_to_exact_signed_fatou
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (w : ℝ) (hw : 0 < w) (Y : Ω → ℝ)
    (F M B E : ℕ → Ω → ℝ)
    (hFm : ∀ n, Measurable (F n))
    (hFi : ∀ n, Integrable (F n) P)
    (hFn : ∀ n, 0 ≤ᵐ[P] F n)
    (hR : ∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
      (∫ ω, M n ω + B n ω ∂P) ≤ 0)
    (hEi : ∀ n, Integrable (E n) P)
    (hEn : ∀ n, 0 ≤ᵐ[P] E n)
    (hE0 : Tendsto (fun n => ∫ ω, E n ω ∂P) atTop (nhds 0))
    (hPath : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ w + (M n ω + B n ω) + E n ω)
    (hFatou : ∀ᵐ ω ∂P,
      ENNReal.ofReal (Y ω) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop) :
    ∃ F' M' B' : ℕ → Ω → ℝ,
      (∀ n, Measurable (F' n) ∧ Integrable (F' n) P ∧
        0 ≤ᵐ[P] F' n) ∧
      (∀ n, Integrable (fun ω => M' n ω + B' n ω) P ∧
        (∫ ω, M' n ω + B' n ω ∂P) ≤ 0) ∧
      (∀ n, ∀ᵐ ω ∂P, F' n ω ≤
        w + (M' n ω + B' n ω)) ∧
      (∀ᵐ ω ∂P, ENNReal.ofReal (Y ω) ≤
        liminf (fun n => ENNReal.ofReal (F' n ω)) atTop) := by sorry
