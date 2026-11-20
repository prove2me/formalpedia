-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_agentB_original_positive_clock_cash_partition_nonnegative_clamp
-- name    : AvramDividend.Classical.avram_agentB_original_positive_clock_cash_partition_nonnegative_clamp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T00:01:30.556918+00:00
-- url     : https://prove2.me/theorems/932914d6-6178-4928-a7b6-eadc4ff588a4
-- title:
--   Original positive stopped-clock discounted cash partition with zero-clipped final interval
-- statement:
--   The original positive ruin-clipped discounted Stieltjes cash before rho is bounded by its true time-zero dividend atom, the strictly interior physical grid cells, and the final crossing strip with nonnegative-real clipped lower bound rho - Delta. The clipped final interval excludes the original zero-time atom, including when rho is shorter than the mesh. This strengthens gledger134 and feeds the exact topcap stopped HJB positive-clock bound.
-- source:
--   Proved gledger134 finite partition proof; substitute a precise clipped crossing strip from avram_agentB_clipped_crossing_strip_inside_nonnegative_final_mesh in the final-cell inclusion step, retain gledger130 cash upper bound, original gledger101 paymentTimes support, and finite-measure toReal conversion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_agentB_original_positive_clock_cash_partition_nonnegative_clamp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (n m : ℕ)
    (ρ : ℝ≥0) (hρn : ρ ≤ (n : ℝ≥0))
    (hρruin : (ρ : ℝ≥0∞) ≤ ruinTime X x D ω)
    (k : ℕ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 2)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    v k < ρ → v (k + 1) = ρ →
    (∀ i : ℕ, i < k → v (i + 1) < ρ) →
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal ≤
      ((dividendMeasure D ω) ({0} : Set ℝ)).toReal +
      (∑ i ∈ Finset.range k,
        (∫⁻ s in Ioc (v i : ℝ) (v (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Ioo ((ρ - Δ : ℝ≥0) : ℝ) (ρ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by sorry
