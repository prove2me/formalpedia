-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_signed_grid_envelope_of_expected_upper
-- name    : AvramDividend.Classical.avram_limit2_signed_grid_envelope_of_expected_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:09:23.597397+00:00
-- url     : https://prove2.me/theorems/a0d02154-aea8-4ca1-a925-7ecb27da9846
-- title:
--   Physical-grid expectation bound yields the signed Fatou F/M/B envelope
-- statement:
--   For a genuine physical stopped-cash grid already known measurable, integrable, nonnegative, dominated in mean by the candidate value, and dominating the actual limit payoff, the canonical signed F/M/B Fatou certificate is obtained algebraically by M_n=F_n-c and B_n=0. No physical stochastic compensator identity is asserted.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_signed_strict_fatou_real_grid_certificate
open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_limit2_signed_grid_envelope_of_expected_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (c : ℝ)
    (F : ℕ → Ω → ℝ) (L : Ω → ℝ≥0∞)
    (hFm : ∀ n, Measurable (F n))
    (hFi : ∀ n, Integrable (F n) P)
    (hFn : ∀ n, 0 ≤ᵐ[P] F n)
    (hConstI : Integrable (fun _ : Ω => c) P)
    (hConstMean : (∫ _ω : Ω, c ∂P) = c)
    (hMean : ∀ n, (∫ ω, F n ω ∂P) ≤ c)
    (hFatou : ∀ᵐ ω ∂P,
      L ω ≤ liminf (fun n => ENNReal.ofReal (F n ω)) atTop) :
    ∃ F' M B : ℕ → Ω → ℝ,
      (∀ n, Measurable (F' n)) ∧
      (∀ n, Integrable (F' n) P) ∧
      (∀ n, 0 ≤ᵐ[P] F' n) ∧
      (∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
        (∫ ω, M n ω + B n ω ∂P) ≤ 0) ∧
      (∀ n, ∀ᵐ ω ∂P,
        F' n ω ≤ c + (M n ω + B n ω)) ∧
      (∀ᵐ ω ∂P,
        L ω ≤ liminf (fun n => ENNReal.ofReal (F' n ω)) atTop) := by sorry
