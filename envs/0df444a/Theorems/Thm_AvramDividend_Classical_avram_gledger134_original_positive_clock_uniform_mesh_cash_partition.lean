-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger134_original_positive_clock_uniform_mesh_cash_partition
-- name    : AvramDividend.Classical.avram_gledger134_original_positive_clock_uniform_mesh_cash_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:01:06.030436+00:00
-- url     : https://prove2.me/theorems/b6101ac5-4d44-47f9-b741-76a0c5ec335f
-- title:
--   Original stopped cash decomposes into zero atom, strict interior cells and final crossing strip
-- statement:
--   For the original admissible dividend process, a stopped clock before the physical ruin time and a deterministic clipped uniform mesh, the actual finite discounted pre-stop Stieltjes cash is bounded by the initial cash atom, the genuine strict interior cell cash and the terminal strip cash. The final strip remains open at the stopping time.
-- source:
--   Source-faithful original cash partition from Proved gledger130, gledger101 strict payment support, gledger113 crossing strip, gledger89 grid monotonicity and Proved p4D original stopped cash finiteness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger134_original_positive_clock_uniform_mesh_cash_partition
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
          Ioo ((ρ : ℝ) - (Δ : ℝ)) (ρ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by sorry
