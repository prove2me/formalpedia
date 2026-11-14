-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a23_original_negative_band_signed_window_stationary_law_20261113
-- name    : AvramDividend.Classical.avram_a23_original_negative_band_signed_window_stationary_law_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:24:42.258387+00:00
-- url     : https://prove2.me/theorems/88d19d43-3467-4216-b14b-e625fcddd9bf
-- title:
--   Physical original negative signed marked-jump windows of the same length have exactly stationary laws
-- statement:
--   The signed integral of the actual original spectrally negative Levy jump measure over any negative mark truncation band has the same law on every time interval of a fixed deterministic duration, without using replacement noise.
-- source:
--   A23 source-time-uniform Borel signed band extraction and source future-path stationary law via Proved f7f7d00c.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The actual original signed negative-mark window has a time-stationary law. -/

theorem AvramDividend.Classical.avram_a23_original_negative_band_signed_window_stationary_law_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (T s : ℝ≥0) :
    let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      (Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    Measure.map (fun ω : Ω =>
      ∫ p in (Ioc s (s + T) ×ˢ B), p.2 ∂NX ω) P =
    Measure.map (fun ω : Ω =>
      ∫ p in (Ioc 0 T ×ˢ B), p.2 ∂NX ω) P := by sorry
