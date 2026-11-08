-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_zero_masked_F_uniform_integrable
-- name    : AvramDividend.Classical.avram_ubv_finite9_original_zero_masked_F_uniform_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:32:58.433241+00:00
-- url     : https://prove2.me/theorems/25eaf4f0-82b7-480c-a73a-31e341f0ad31
-- title:
--   Uniform integrability of the original finite-cap stopped payoff after zero-clock masking
-- statement:
--   For the original Levy process, stopped post-right-dividend reserve and inclusive closed-clock cash at every subclock of the finite-cap ruin-limited horizon, replace the time-zero payoff by the initial candidate value. Under the same full-family integrable envelope, actual stopping-time measurability and original payoff integrability, the entire masked payoff family is uniformly integrable. The proof dominates every masked absolute value by the integrable full-payoff envelope plus the initial candidate absolute value. This is useful when converting finite-grid positive-clock stochastic budgets into expected upper bounds without changing the zero-clock atom.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_F_family_integrable_envelope
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_rightcont_stopping_zero_mask_integrable
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Tactic.NormNum

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_finite9_original_zero_masked_F_uniform_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (hfinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0)
    (hCashτI : Integrable
      (fun ω => (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) P)
    (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P) :
    UniformIntegrable (fun k ω => if σ k ω = 0 then w x else F k ω)
      (1 : ℝ≥0∞) P := by sorry
