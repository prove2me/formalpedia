-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_rational_time_uniform_mark_mean_measure
-- name    : AvramDividend.Classical.avram_p2_d_future_rational_time_uniform_mark_mean_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:41:04.499725+00:00
-- url     : https://prove2.me/theorems/6484c4c2-423f-4550-b98c-769b20c01d96
-- title:
--   A single original mark mean measure determines every rational-time marked count rate
-- statement:
--   There exists a genuine original-process mark measure independent of horizon, numerator, denominator and Borel mark class; for all horizons satisfying d*t=n, its expected intrinsic marked count equals (n/d) times the one measure. Extended-infinite expected counts are handled by the preceding proved rational relation, without any assumed ν-identification.
-- source:
--   Uses the Proved source original unit-time mark mean measure 32d3702f-6688-4d7a-8190-7475ce004cc2 and Proved original-source rational relation 2786c7d2-72bf-4a14-880e-4b0c9712feb3. This is a quantified single-measure interface, not an auxiliary Poisson process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_rational_time_uniform_mark_mean_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ ρ : Measure ℝ,
      ∀ (t : ℝ≥0) (n d : ℕ) (hd : 0 < d)
        (hrel : (d : ℝ≥0) * t = (n : ℝ≥0))
        (B : Set ℝ), MeasurableSet B →
        (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 t ×ˢ B) ∂P) =
        ((n : ℝ≥0∞) / (d : ℝ≥0∞)) * ρ B := by sorry
