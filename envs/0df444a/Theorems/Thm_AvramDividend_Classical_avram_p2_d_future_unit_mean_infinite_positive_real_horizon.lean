-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_unit_mean_infinite_positive_real_horizon
-- name    : AvramDividend.Classical.avram_p2_d_future_unit_mean_infinite_positive_real_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:27:22.647283+00:00
-- url     : https://prove2.me/theorems/51f3c26d-41e0-4902-936c-3f49659153fc
-- title:
--   Infinite first-unit original marked mean forces infinite count mean at every positive real horizon
-- statement:
--   For an arbitrary Borel mark set on the actual spectrally negative Lévy sample path, infinite expected intrinsic jump count over (0,1] forces infinite expected count over every strictly positive real horizon. Uses original count monotonicity, natural horizon scaling and Archimedean multiplication. Treats t=0 separately, since zero times infinity is zero.
-- source:
--   Source original M_B(t) with Proved monotonicity d6f0bf62 and Proved scaling for natural multiples aeac15b4; choose n with 1≤n*t and use the fact finite n times finite ENNReal cannot be top. No ν identification or substitute Poisson construction.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_unit_mean_infinite_positive_real_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) (hB : MeasurableSet B)
    (t : ℝ≥0) (hpos : 0 < t)
    (hunit : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) = ⊤) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ B) ∂P) = ⊤ := by sorry
