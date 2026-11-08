-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_F_family_integrable_envelope
-- name    : AvramDividend.Classical.avram_ubv_finite9_original_F_family_integrable_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:53:48.703018+00:00
-- url     : https://prove2.me/theorems/23084b1e-7b8b-4e94-8894-84847ce8a6c8
-- title:
--   Common integrable dominating envelope for original finite-cap stopped value-plus-cash
-- statement:
--   Uniform finite cap control of exact post-right-payment w(Wσ), plus discount exp(-qσ)≤1 and monotonicity of inclusive closed-clock dividend cash under σk≤τ, bounds every true Fk pathwise by one deterministic constant plus final closed-clock Cashτ. This envelope is integrable when the source Cashτ is integrable. It preserves time-zero and horizon atoms, and does not assert mean-zero martingales.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_finite9_original_F_family_integrable_envelope
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
        ∂(dividendMeasure D ω)).toReal) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ k ω, |F k ω| ≤ B +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) ∧
      Integrable (fun ω => B +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) P := by sorry
