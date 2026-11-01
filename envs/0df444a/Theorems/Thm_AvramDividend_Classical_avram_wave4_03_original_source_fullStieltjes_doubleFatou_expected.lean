-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_source_fullStieltjes_doubleFatou_expected
-- name    : AvramDividend.Classical.avram_wave4_03_original_source_fullStieltjes_doubleFatou_expected
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:51:28.181094+00:00
-- url     : https://prove2.me/theorems/1f91129d-aba5-44e0-96dc-a2af6dfeb3e0
-- title:
--   Actual source Lévy double-Fatou passage from dyadic Stieltjes mesh to full expected dividend integral
-- statement:
--   For original spectrally negative Lévy X and the same adapted left-continuous D, expected full Stieltjes integral of the post-payment discounted exponential over (0,T] is bounded by lower limit of expected right upper-dyadic Stieltjes approximations. Two genuine Fatou applications are justified: pathwise source cadlag and exact full random Stieltjes kernel, then measurability of each random mesh integral using the original source joint time-probability integrand and globally s-finite dividendMeasure kernel. No replacement PRM and no atom concentration hypothesis.
-- source:
--   Proved original-source right-dyadic pathwise full Stieltjes Fatou 2a53d9e3 (required as import), joint source integrand 30c00aaa and global random Stieltjes s-finite kernel 766b5129.

import Mathlib
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_source_rightDyadic_fullStieltjes_fatou
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_source_postPayment_discounted_exponential_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists

open MeasureTheory Set Filter ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_original_source_fullStieltjes_doubleFatou_expected {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ q : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ s : ℝ, if s ∈ Ioc (0 : ℝ) (T : ℝ) then
      ENNReal.ofReal (Real.exp (θ * (x + X.X s.toNNReal ω -
        rightLimit D s.toNNReal ω) - (s.toNNReal : ℝ) * q))
      else 0 ∂dividendMeasure D ω ∂P) ≤
    Filter.liminf (fun n : ℕ => ∫⁻ ω, ∫⁻ s : ℝ,
      if s ∈ Ioc (0 : ℝ) (T : ℝ) then
        let k := Nat.ceil (((s.toNNReal / T : ℝ≥0) : ℝ) * (2 : ℝ) ^ n)
        let u := ((k : ℝ≥0) / (2 : ℝ≥0) ^ n) * T
        ENNReal.ofReal (Real.exp (θ * (x + X.X u ω -
          rightLimit D u ω) - (u : ℝ) * q))
      else 0 ∂dividendMeasure D ω ∂P) atTop := by sorry
