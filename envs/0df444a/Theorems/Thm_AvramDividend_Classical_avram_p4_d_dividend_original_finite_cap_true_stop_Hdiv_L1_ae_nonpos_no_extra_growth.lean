-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_finite_cap_true_stop_Hdiv_L1_ae_nonpos_no_extra_growth
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_finite_cap_true_stop_Hdiv_L1_ae_nonpos_no_extra_growth
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:41:31.302903+00:00
-- url     : https://prove2.me/theorems/d09fde6a-c300-4309-8975-d72fffcbabf8
-- title:
--   Original finite-cap source stopped full-Stieltjes signed dividend budget without additional value-growth hypotheses
-- statement:
--   For the exact original controlled Lévy process, admissible finite cap, positive reserve, true ruin-truncated stopping clock, source W/Cash/Term/Hdiv, continuous candidate with interior slope≥1 and actual integrable Cash/Term, construct the formerly auxiliary exponential growth envelope from the source cap itself. Conclude that the original full-Cash signed dividend remainder is integrable and a.e. nonpositive, with time zero, singular-continuous mass, simultaneous right-jumps and closed horizon preserved. Stopped-X measurability remains visible; P4-F retains stochastic martingale and boundary obligations.
-- source:
--   New original source full signed Hdiv theorem and automatic finite-cap growth envelope; source exact original W Cash Term and ruin-clock definitions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_finite_cap_linear_extension_exponential_envelope_exists
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_preruin_branch_measurable_from_clock
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_piecewise_postpayment_caplinear_L1_from_discounted_Term
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_raw_caplinear_value_L1_of_exp_envelope
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_branch_L1_ae_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04b_cap_extension_measurable_of_zero_negative

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_finite_cap_true_stop_Hdiv_L1_ae_nonpos_no_extra_growth
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hCfin : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z else
        w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (τ : Ω → ℝ≥0) (H : ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω : Ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ H)
    (hXstopped : Measurable (fun ω => X.X (τ ω) ω))
    (W Cash Term Hdiv : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω then
      x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (hCashI : Integrable Cash P)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermI : Integrable Term P)
    (hHdiv : ∀ ω, Hdiv ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        Cash ω + (V (W ω) - V (x + X.X (τ ω) ω))
      else 0) :
    Integrable Hdiv P ∧ ∀ᵐ ω ∂P, Hdiv ω ≤ 0 := by sorry
