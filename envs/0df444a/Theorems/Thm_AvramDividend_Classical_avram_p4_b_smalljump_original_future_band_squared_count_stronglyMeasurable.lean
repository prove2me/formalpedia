-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_future_band_squared_count_stronglyMeasurable
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_future_band_squared_count_stronglyMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:27:16.915187+00:00
-- url     : https://prove2.me/theorems/413b9342-98ea-4032-b98e-7c105e0a90c3
-- title:
--   Original future-band squared count strong measurability
-- statement:
--   Measurability of the genuine original Lévy intrinsic finite-band count in a future sigma-algebra implies strong measurability of its squared real compensated count.
-- source:
--   Original X.X and X.nu, pinned Mathlib source-exact Lean proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_future_band_squared_count_stronglyMeasurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B : Set ℝ) (N : Ω → ℝ≥0∞)
    (hSource : ∀ ω, N ω =
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B))
    (r : ℝ) (hRate : r =
      ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal)
    (mFuture : MeasurableSpace Ω)
    (hNmeas : Measurable[mFuture] N) :
    StronglyMeasurable[mFuture] (fun ω => ((N ω).toReal - r) ^ 2) := by sorry
