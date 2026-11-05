-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_finite_cap_full_stieltjes_Hdiv_integrable_and_expected_nonpositive
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_finite_cap_full_stieltjes_Hdiv_integrable_and_expected_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T01:09:21.200989+00:00
-- url     : https://prove2.me/theorems/f0e1bd6d-757b-461a-b3a3-2a839cf60de4
-- title:
--   Original finite-cap closed-Stieltjes dividend remainder has finite nonpositive mean
-- statement:
--   At P4-F genuine physical controlled X/D stopped at min(ruinTime,n), finite cap, original closed dividendMeasure Cash (including valid zero and horizon atoms), original W and discounted Term and exact source Hdiv, show Integrable Hdiv and its actual Bochner integral is nonpositive. Uses the already Proved original source no-extra-stopped-X-meas Hdiv a.e. sign and Mathlib integral_nonpos_of_ae; no circular martingale or HJB assumptions.
-- source:
--   Proved source exact P4-D Hdiv L1 and a.e. sign 11dbb659, pinned Mathlib integral_nonpos_of_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_finite_cap_full_stieltjes_Hdiv_L1_nonpos_without_stopped_state_measurability

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_finite_cap_full_stieltjes_Hdiv_integrable_and_expected_nonpositive
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
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω : Ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
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
    (hTermMeas : AEStronglyMeasurable Term P)
    (hHdiv : ∀ ω, Hdiv ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        Cash ω + (V (W ω) - V (x + X.X (τ ω) ω))
      else 0) :
    Integrable Hdiv P ∧ (∫ ω, Hdiv ω ∂P) ≤ 0 := by sorry
