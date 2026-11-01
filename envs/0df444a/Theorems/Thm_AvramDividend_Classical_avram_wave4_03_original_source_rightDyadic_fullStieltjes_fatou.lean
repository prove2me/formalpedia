-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_source_rightDyadic_fullStieltjes_fatou
-- name    : AvramDividend.Classical.avram_wave4_03_original_source_rightDyadic_fullStieltjes_fatou
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:15:29.619316+00:00
-- url     : https://prove2.me/theorems/2a53d9e3-f853-4371-8130-c91597eaf43c
-- title:
--   Original controlled Lévy source: right-dyadic full Stieltjes dividend integral satisfies pathwise Fatou
-- statement:
--   On the true original spectrally negative Lévy sample path with the same adapted left-continuous dividend D, the full Stieltjes integral of the discounted post-payment exponential source value over the positive finite horizon is bounded by liminf of its upper right-dyadic time-mesh Stieltjes integrals. This uses the genuine source path cadlag/right-mesh convergence and countable Fatou, with diffuse and singular-continuous payments retained because the measure is not replaced by a right-jump sum.
-- source:
--   Accepted original controlled postpayment source right-dyadic convergence 608b8b12 and genuine source jointly measurable 30c00aaa; Mathlib lintegral_liminf_le.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_source_postPayment_exponential_dyadic_rightMesh_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_source_postPayment_discounted_exponential_joint_time_path_measurable

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_original_source_rightDyadic_fullStieltjes_fatou
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (θ q : ℝ) (ω : Ω) (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ s : ℝ, if s ∈ Ioc (0 : ℝ) (T : ℝ) then
      ENNReal.ofReal (Real.exp
        (θ * (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) -
          (s.toNNReal : ℝ) * q)) else 0 ∂dividendMeasure D ω) ≤
    Filter.liminf
      (fun n : ℕ => ∫⁻ s : ℝ,
        if s ∈ Ioc (0 : ℝ) (T : ℝ) then
          let k := Nat.ceil (((s.toNNReal / T : ℝ≥0) : ℝ) * (2 : ℝ) ^ n)
          let u := ((k : ℝ≥0) / (2 : ℝ≥0) ^ n) * T
          ENNReal.ofReal (Real.exp
            (θ * (x + X.X u ω - rightLimit D u ω) - (u : ℝ) * q))
        else 0 ∂dividendMeasure D ω) atTop := by sorry
