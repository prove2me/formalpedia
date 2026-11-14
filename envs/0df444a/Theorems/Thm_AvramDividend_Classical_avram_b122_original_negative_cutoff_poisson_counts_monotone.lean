-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b122_original_negative_cutoff_poisson_counts_monotone
-- name    : AvramDividend.Classical.avram_b122_original_negative_cutoff_poisson_counts_monotone
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T17:21:14.297958+00:00
-- url     : https://prove2.me/theorems/0820f966-f2f9-4863-8ed5-5f269f2abe45
-- title:
--   Original negative-jump marked Poisson source counts are monotone in the reciprocal band cutoff on any physical interval
-- statement:
--   Fix a path of the original spectrally negative Levy source and an exact physical half-open interval. The original mapped source negative-jump Poisson measure count over the band of all marks up to -1/(n+1) is at most the original count over the band up to -1/(m+1) for n≤m. The proof uses inclusion of the marked space-time rectangles and monotonicity of the very same original source measure. This is the count-level monotonicity needed to combine finite-band zero source count, cutoff exhaustion and genuine finite stopped-grid marked cells.
-- source:
--   Original SpectrallyNegativeLevy mapped negative source jump measure and Mathlib MeasureTheory.measure_mono.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine original negative-mark source Poisson counts increase along cofinal reciprocal cutoffs on physical intervals. -/

theorem AvramDividend.Classical.avram_b122_original_negative_cutoff_poisson_counts_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) ≤
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iic (-(1 / ((m : ℝ) + 1)))) := by sorry
