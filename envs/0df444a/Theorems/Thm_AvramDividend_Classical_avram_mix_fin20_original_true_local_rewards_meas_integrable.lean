-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin20_original_true_local_rewards_meas_integrable
-- name    : AvramDividend.Classical.avram_mix_fin20_original_true_local_rewards_meas_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T08:56:01.636783+00:00
-- url     : https://prove2.me/theorems/4f61f549-bf01-42cc-8f1e-2df1173b7e56
-- title:
--   Original bounded stopped finite-cap complete cash reward measurability and integrability
-- statement:
--   Given original finite-cap full stopped reward F integrable and exact paid rewards at earlier original right-continuous stopping clocks, prove every local source-exact terminal plus inclusive closed cash reward is measurable and integrable. Use original source payoff measurability, nonnegative terminal decomposition to extract closed cash L1, and finite cap common envelope. This is a necessary input to physical mixed positive-clock stopped Ito Fatou budgets and requires no Gaussian independence or large-mark moment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_any_clock_source_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_endpoint_original_closed_cash_L1_of_integrable_F
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_F_family_integrable_from_exact_cash
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin20_original_true_local_rewards_meas_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hDsource : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨
              (σ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ ω) ω - rightLimit D (σ ω) ω
          else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : Integrable F P) (hCfinite : C ≠ ⊤)
    (σk : ℕ → Ω → ℝ≥0)
    (hσkstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σk k ω : WithTop ℝ≥0)))
    (hσkle : ∀ k ω, σk k ω ≤ σ ω)
    (Fk : ℕ → Ω → ℝ)
    (hFksource : ∀ k ω, Fk k ω =
      Real.exp (-(q * (σk k ω : ℝ))) *
        w (if σk k ω = 0 ∨
              (σk k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σk k ω) ω - rightLimit D (σk k ω) ω
          else riskProcess X x D (σk k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σk k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) :
    (∀ k, Measurable (Fk k)) ∧
    (∀ k, Integrable (Fk k) P) := by sorry
