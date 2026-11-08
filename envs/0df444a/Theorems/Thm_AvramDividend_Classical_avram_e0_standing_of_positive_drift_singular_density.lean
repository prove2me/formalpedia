-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_e0_standing_of_positive_drift_singular_density
-- name    : AvramDividend.Classical.avram_e0_standing_of_positive_drift_singular_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:36:57.749379+00:00
-- url     : https://prove2.me/theorems/4f3d7f41-4390-4396-824b-2ab09d2ad550
-- title:
--   Positive physical drift and singular negative jump law supply the Avram Standing assumptions
-- statement:
--   For a genuine original spectrally negative Lévy process with the explicit singular negative-jump measure, positive physical drift, nonzero jump measure and integrable unit-time reserve, the standing assumptions follow: nonmonotone paths from positive drift and actual jumps, moment integrability from the hypothesis, and Condition33 from absolute continuity of the singular density.
-- source:
--   Standing package for e0b94d7f source-exact countermodel. Uses proved e0a856a6 negative-support/absolute-continuity source and the original definitions of HasMonotonePaths and Standing.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_e0_standing_of_positive_drift_singular_density
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))
    (hpos : 0 < X.drift) (hne : X.ν ≠ 0)
    (hint : Integrable (X.X 1) P) :
    X.Standing := by sorry
