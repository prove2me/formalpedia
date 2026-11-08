-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps10_original_negative_band_exponential_L2_of_law
-- name    : AvramDividend.Classical.avram_ubv_ito_jumps10_original_negative_band_exponential_L2_of_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:35:54.21708+00:00
-- url     : https://prove2.me/theorems/6b3b6bf9-52d4-472e-8f88-9aa65db0654c
-- title:
--   Actual Levy negative-band count has all real exponential L2 moments under its Poisson law
-- statement:
--   The exact actual intrinsic negative-jump count NB of the unchanged original Levy source has square-integrable exponential power for every real base, conditional on its genuine measurable Poisson(r) original-space law. Transport the proved Poisson L2 moment through the measurable count map; do not replace X or infer a finite-activity intensity for the full Levy jump measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps10_poisson_exponential_power_memLp_two

open Classical MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_ito_jumps10_original_negative_band_exponential_L2_of_law
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
    (a : ℝ) : MemLp (fun ω => a ^ NB ω) 2 P := by sorry
