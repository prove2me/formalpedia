-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_finite_cap_original_expected_budget_to_exact_witness
-- name    : AvramDividend.Classical.avram_p4_f_assembly_finite_cap_original_expected_budget_to_exact_witness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:08:30.474505+00:00
-- url     : https://prove2.me/theorems/3ed91760-17b3-4763-96f9-23d0d8b34c11
-- title:
--   Original finite-cap canonical MGH witnesses follow from the exact stopped expected budget with no terminal L1 premise
-- statement:
--   For the actual original source X, true postpayment-or-ruin W, full discounted Stieltjes Cash and exact discounted Term under finite cap, the canonical continuity, zero extension, admissibility and terminal measurability assumptions automatically provide Integrable Term using the independently Proved finite-cap source result. If the exact expected stopped Term+Cash upper bound has separately been proved, the previously accepted original law centring theorem yields the full canonical Integrable M/G/H, zero mean, joint nonpositive residual and full a.e. pathwise inequality. This is a conditional direct-expectation fallback; the expected budget remains a genuinely unproved input and the canonical 0dda is not submitted.
-- source:
--   P4-F finite cap terminal L1 helper; P4-F accepted direct expectation-to-witness b77e6dae-ae3a-4f0d-8f93-97a107f92dc9; original Avram Prop. 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_finite_cap_stopped_terminal_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_expected_budget_witness_of_original_L1
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_finite_cap_original_expected_budget_to_exact_witness
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (τ : Ω → ℝ≥0) (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (hBudget : (∫ ω, Term ω + Cash ω ∂P) ≤ w x) :
    ∃ M G H : Ω → ℝ,
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω) := by sorry
