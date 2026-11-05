-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_finite_cap_full_stieltjes_Hdiv_L1_nonpos_of_P4F_Term_aemeasurable
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_finite_cap_full_stieltjes_Hdiv_L1_nonpos_of_P4F_Term_aemeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:40:45.787785+00:00
-- url     : https://prove2.me/theorems/e32c27a2-f0f7-4b31-bf2d-f1f3a13ea3a2
-- title:
--   Actual original stopped finite-cap Hdiv is integrable and nonpositive from P4-F terminal measurability
-- statement:
--   At P4-F literal original finite cap and ruin-truncated clock, replace auxiliary terminal L1 and deterministic stopping-bound assumptions by P4-F actual AEStronglyMeasurable Term and source tau=min(ruin,n). The existing Proved original P4-F finite-cap terminal integrability and new exact-clock bound discharge both, leaving the actual original closed Stieltjes Cash, same-source physical stopped-X measurability and derivative only at interior states. The conclusion is Integrable Hdiv and Hdiv≤0 almost everywhere; the original Ito and HJB expectation terms remain separate.
-- source:
--   Proved P4-F source finite-cap terminal L1 f11748f4, true source finite clock bound and Proved signed full-Stieltjes finite-cap Hdiv d09fde6a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_le_finite_horizon
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_ennreal_finite_cap_stopped_terminal_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_finite_cap_true_stop_Hdiv_L1_ae_nonpos_no_extra_growth

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_finite_cap_full_stieltjes_Hdiv_L1_nonpos_of_P4F_Term_aemeasurable
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
    (hTermMeas : AEStronglyMeasurable Term P)
    (hHdiv : ∀ ω, Hdiv ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        Cash ω + (V (W ω) - V (x + X.X (τ ω) ω))
      else 0) :
    Integrable Hdiv P ∧ ∀ᵐ ω ∂P, Hdiv ω ≤ 0 := by sorry
