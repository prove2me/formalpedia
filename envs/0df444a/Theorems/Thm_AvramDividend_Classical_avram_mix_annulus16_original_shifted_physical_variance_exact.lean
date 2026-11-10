-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_annulus16_original_shifted_physical_variance_exact
-- name    : AvramDividend.Classical.avram_mix_annulus16_original_shifted_physical_variance_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T22:43:31.269671+00:00
-- url     : https://prove2.me/theorems/99d7b9e5-0829-4d13-b64b-02a7cf4ece97
-- title:
--   Physical annulus centred second moment exact on every shifted original-time window
-- statement:
--   For the original spectrally negative Lévy path and genuine marked jump measure, the compensated negative-annulus count over (s,s+T] is square-integrable and has variance exactly T times the original annulus Lévy rate. This follows by transporting the Proved physical zero-origin variance through the Proved original marked-count moment stationarity; it supplies the time-shifted quantitative input to right-continuous predictable stopped-grid isometry.
-- source:
--   Root-connected 6e234a3f original variance and 34cdb144 exact shifted marked count law; consumer the conditional original-filtration annulus second moment for 5f12c023.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_physical_annulus_count_variance_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_intrinsic_marked_real_moment_stationary
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_annulus16_original_shifted_physical_variance_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => ((N ω).toReal - r) ^ 2) P ∧
      (∫ ω, ((N ω).toReal - r) ^ 2 ∂P) = r := by sorry
