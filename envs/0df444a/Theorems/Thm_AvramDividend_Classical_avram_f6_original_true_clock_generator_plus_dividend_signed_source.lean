-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_true_clock_generator_plus_dividend_signed_source
-- name    : AvramDividend.Classical.avram_f6_original_true_clock_generator_plus_dividend_signed_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T10:06:20.245229+00:00
-- url     : https://prove2.me/theorems/2f0ccd3b-a4a9-44f0-a2f0-ca1574045aca
-- title:
--   Original true-clock HJB generator plus full Stieltjes dividend drop joint signed source
-- statement:
--   At an actual zero or strictly pre-ruin subordinate stopping clock of the original capped spectrally negative Levy and dividend strategy, the genuinely physical discounted generator drift integral up to the stop plus actual discounted full Stieltjes cash and caplinear pre-/post-payment value change is nonpositive pathwise. The generator uses original left-limit controlled risk and HJB, with explicit actual integrability; the cash uses original dividendMeasure/rightLimit D and [0,σ] including zero. This assembles two proven signed components of common Ito, leaving centred Gaussian/negative-jump gains and ruin-contact residual as separate stochastic obligations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_true_clock_generator_plus_dividend_signed_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : ℕ → Ω → ℝ≥0) (k : ℕ) (μ : Measure ℝ≥0)
    (hGInt : ∀ ω : Ω, Integrable
      (fun t : ℝ≥0 =>
        let Y : ℝ := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        if 0 < Y ∧ ENNReal.ofReal Y < C ∧ t ≤ σ k ω then
          Real.exp (-(q * (t : ℝ))) *
            (X.generator w Y - q * w Y)
        else 0) μ)
    (ω : Ω) (hPre : σ k ω = 0 ∨
      (σ k ω : ℝ≥0∞) < ruinTime X x D ω) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z
      else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    (∫ t : ℝ≥0,
      let Y : ℝ := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
      if 0 < Y ∧ ENNReal.ofReal Y < C ∧ t ≤ σ k ω then
        Real.exp (-(q * (t : ℝ))) *
          (X.generator w Y - q * w Y)
      else 0 ∂μ) +
    ((∫⁻ s in Icc (0 : ℝ) (σ k ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)).toReal +
      (V (x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω) -
       V (x + X.X (σ k ω) ω))) ≤ 0 := by sorry
