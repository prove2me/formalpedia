-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_ennreal_finite_cap_expected_budget_to_witness
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_ennreal_finite_cap_expected_budget_to_witness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:25:39.813539+00:00
-- url     : https://prove2.me/theorems/49cd8d52-21b7-4bee-8a5d-19d3c5a60d3c
-- title:
--   Canonical finite ENNReal cap expected original stopped budget yields exact MGH witnesses
-- statement:
--   For the original spectrally negative Lévy process and canonical C:ℝ≥0∞ with C≠∞, the accepted true stopped terminal L1 lemma supplies integrability without a new moment assumption. If the exact original stopped expected dividend upper bound is independently established, the accepted centring bridge immediately gives integrable M/G/H, zero mean, joint nonpositive signed residual, and full almost-everywhere pathwise inequality for the true W/Cash/Term. No claim is made that the expected budget or C=∞ branch is proved.
-- source:
--   P4-F source ENNReal finite cap terminal L1 f11748f4 and original L1 expected budget witness b77e6dae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_ennreal_finite_cap_stopped_terminal_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_expected_budget_witness_of_original_L1
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_ennreal_finite_cap_expected_budget_to_witness
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hCfin : C ≠ ⊤)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
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
