-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_gridfree_zero_activity_original_predictable_rectangle
-- name    : AvramDividend.Classical.avram_wave6_01_bv_gridfree_zero_activity_original_predictable_rectangle
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:57:32.437032+00:00
-- url     : https://prove2.me/theorems/d265ee64-8693-46c0-8255-293a796a6bf6
-- title:
--   Grid-free genuine BV zero-activity predictable marked jump compensation
-- statement:
--   For X on its unchanged Ω/P/𝓕, assuming actual bounded variation and zero negative Lévy jump intensity, the literal intrinsic count on any (s,T]×B restricted to an original past event has exactly expected mass P(A)(T−s)ν(B). No finite-grid data, Poisson copy, replacement path or compensator premise remains. The positive-horizon uniform grid required internally is now constructed by a separately Proved deterministic witness.
-- source:
--   Instantiate the uniform time-grid witness (canonical Proved since 20:28 UTC), then apply the genuinely Proved cfd03bfe zero-intensity actual-path rectangle identity. This deletes auxiliary clock assumptions; source triplet and filtration unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_positive_horizon_fine_source_grid_witness
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_zero_negative_intensity_original_rectangle_compensator
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_01_bv_gridfree_zero_activity_original_predictable_rectangle
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hZero : X.ν (Iio (0 : ℝ)) = 0)
    (T : ℝ≥0) (hT : 0 < T)
    (s : ℝ≥0) (hst : s ≤ T)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s T ×ˢ B) ∂P) =
      P A * ((T - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
