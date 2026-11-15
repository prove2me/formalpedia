-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b25_geometric_L1_two_gain_integrable_ae_envelopes
-- name    : AvramDividend.Classical.avram_b25_geometric_L1_two_gain_integrable_ae_envelopes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T01:05:05.512743+00:00
-- url     : https://prove2.me/theorems/524f2c2e-be5e-4793-a929-3b2e4d905a3a
-- title:
--   Geometric L1 increments of two integrable gains give integrable dominators and almost-sure absolute summability
-- statement:
--   Given two integrable function sequences whose successive difference norms have expected values bounded by 2^-k, construct integrable pathwise envelopes dominating all gain norms and show that almost every path has summable absolute increments, simultaneously for both sequences. Use nonnegative Tonelli, integrability of the initial gains and telescoping. This is the core analytic bound for original B25 Gaussian and compensated small-jump gains.
-- source:
--   Avram B25 source splitting of 9f9f4af7, classical Tonelli plus geometric summation; the gain functions remain arbitrary, with no model simplification.

import Mathlib
open MeasureTheory Filter Topology
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_b25_geometric_L1_two_gain_integrable_ae_envelopes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (G J : ℕ → Ω → ℝ)
    (hGI : ∀ k, Integrable (G k) P)
    (hJI : ∀ k, Integrable (J k) P)
    (hGgeom : ∀ k, (∫ ω, ‖G (k + 1) ω - G k ω‖ ∂P)
      ≤ ((1 : ℝ) / 2) ^ k)
    (hJgeom : ∀ k, (∫ ω, ‖J (k + 1) ω - J k ω‖ ∂P)
      ≤ ((1 : ℝ) / 2) ^ k) :
    ∃ (BG BJ : Ω → ℝ),
      Integrable BG P ∧ Integrable BJ P ∧
      (∀ᵐ ω ∂P, Summable
        (fun k : ℕ => ‖G (k + 1) ω - G k ω‖)) ∧
      (∀ᵐ ω ∂P, Summable
        (fun k : ℕ => ‖J (k + 1) ω - J k ω‖)) ∧
      (∀ k, ∀ᵐ ω ∂P, ‖G k ω‖ ≤ BG ω) ∧
      (∀ k, ∀ᵐ ω ∂P, ‖J k ω‖ ≤ BJ ω) := by sorry
