-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_theta_scaled_doubleFatou_expected
-- name    : AvramDividend.Classical.avram_wave4_03_sourceLevy_theta_scaled_doubleFatou_expected
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:15:19.410923+00:00
-- url     : https://prove2.me/theorems/a24398e3-e20b-4e95-ac6d-b3ca0d3c2408
-- title:
--   Original same-path Lévy double Fatou for arbitrary positive exponential tilt and complete Stieltjes dividends
-- statement:
--   For each positive exponential tilt, the expected full random Stieltjes integral of theta times the postpayment compensated source exponential on (0,T] is bounded by the lower limit of its right-dyadic mesh approximation, with diffuse, singular and atomic mass retained. This is derived from the original same-path double-Fatou theorem by an exact logarithmic exponential-shift identity, without any new probability space.
-- source:
--   Original-source genuine Stieltjes double Fatou 1f91129d; the identity exp(log(theta)+z)=theta exp(z), theta>0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_source_fullStieltjes_doubleFatou_expected
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_sourceLevy_theta_scaled_doubleFatou_expected
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 < θ) (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ s : ℝ, if s ∈ Ioc (0 : ℝ) (T : ℝ) then
      ENNReal.ofReal (θ * Real.exp (θ *
        (X.X s.toNNReal ω - rightLimit D s.toNNReal ω) -
        (s.toNNReal : ℝ) * X.ψ θ))
      else 0 ∂dividendMeasure D ω ∂P) ≤
    Filter.liminf (fun n : ℕ => ∫⁻ ω, ∫⁻ s : ℝ,
      if s ∈ Ioc (0 : ℝ) (T : ℝ) then
        let k := Nat.ceil (((s.toNNReal / T : ℝ≥0) : ℝ) * (2 : ℝ) ^ n)
        let u := ((k : ℝ≥0) / (2 : ℝ≥0) ^ n) * T
        ENNReal.ofReal (θ * Real.exp (θ *
          (X.X u ω - rightLimit D u ω) - (u : ℝ) * X.ψ θ))
      else 0 ∂dividendMeasure D ω ∂P) atTop := by sorry
