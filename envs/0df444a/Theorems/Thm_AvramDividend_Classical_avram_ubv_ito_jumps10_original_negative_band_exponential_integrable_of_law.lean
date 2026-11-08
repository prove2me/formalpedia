-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps10_original_negative_band_exponential_integrable_of_law
-- name    : AvramDividend.Classical.avram_ubv_ito_jumps10_original_negative_band_exponential_integrable_of_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:24:46.762207+00:00
-- url     : https://prove2.me/theorems/a5794a34-2654-4b81-92ed-f9e21030246b
-- title:
--   Actual Levy finite-band count has all real exponential L1 moments under its Poisson law
-- statement:
--   For the actual intrinsic negative-band jump count of the unchanged original spectrally negative Levy process, its explicit measurable Poisson(r) law implies that the real random variable a^NB is P-integrable for every a. This is an L1 transport through the genuine original count law, with no claim to construct that law from the Levy standing assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps10_poisson_power_integrable

open Classical MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_ito_jumps10_original_negative_band_exponential_integrable_of_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (B : Set ℝ)
    (NB : Ω → ℕ)
    (hcount : ∀ ω, (NB ω : ℝ≥0∞) =
      ((Measure.count.restrict
        {u : ℝ≥0 | 0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 =>
          (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Set.Ioc (0 : ℝ≥0) T ×ˢ B))
    (hNm : Measurable NB)
    (r : ℝ≥0)
    (hLaw : P.map NB = poissonMeasure r)
    (a : ℝ) : Integrable (fun ω => a ^ NB ω) P := by sorry
