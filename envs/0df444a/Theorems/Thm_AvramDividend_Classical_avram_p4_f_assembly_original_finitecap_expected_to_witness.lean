-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_finitecap_expected_to_witness
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_finitecap_expected_to_witness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:34:51.899211+00:00
-- url     : https://prove2.me/theorems/0d830402-b00f-444d-a1d7-793c56237085
-- title:
--   Original finite-cap UBV expected budget supplies genuine integrable signed witnesses
-- statement:
--   At the actual original finite cap and literal piecewise postpayment stopped reserve W, canonical continuity and zero extension of w imply global integrability of Term, using the already-proved source terminal bound. If an independent source expected stopped cash upper bound has been established, construct the exact three integrable signed witnesses of P4-F using the proved source probability-law centring argument. This is an explicit finite-cap alternative interface and does not assert the missing expected inequality.
-- source:
--   Accepted original finite-cap terminal L1 d5ea6491 and source signed expected-budget witness b77e6dae. No independent process, stronger Ito hypothesis or extra axiom.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_finitecap_terminal_global_L1_auto_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_expected_budget_witness_of_original_L1
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_finitecap_expected_to_witness
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q c : ℝ) (hq : 0 < q) (hc : 0 ≤ c)
    (C : ℝ≥0∞) (hC : C = ENNReal.ofReal c)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (w : ℝ → ℝ) (hwCont : ContinuousOn w (Ici 0))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (Cash Term : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (hExpected : (∫ ω, Term ω + Cash ω ∂P) ≤ w x) :
    ∃ M G H : Ω → ℝ,
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤
        w x + M ω + G ω + H ω) := by sorry
