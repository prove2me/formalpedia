-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_original_negative_Borel_physical_twojump_collision_bound_20261115
-- name    : AvramDividend.Classical.avram_a25_original_negative_Borel_physical_twojump_collision_bound_20261115
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T15:04:50.373256+00:00
-- url     : https://prove2.me/theorems/4ced9f55-3279-4a62-9c0e-61c8454993ae
-- title:
--   Original Lévy negative-Borel physical jump collision probability is at most half the squared expected count
-- statement:
--   For any measurable negative Borel mark set B of finite Lévy intensity and any physical time horizon T, let N count actual original Lévy process jumps on (0,T] with marks in B, and r=Tν(B). The original P-probability of at least two physical jumps is at most r²/2. This uses the already-Proved exact original second falling-factorial moment for B and the original measurable natural-count realisation, together with the generic two-jump occupancy integral bound. It provides a source-faithful quadratic Bernoulli-cell collision estimate for proving the physical count Poisson law without constructing an independent driver.
-- source:
--   Proved source original first/second factorial count 6d1258a3, natural physical count realisation 84a4791e, and generic two-jump moment occupancy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a25_original_negative_Borel_physical_twojump_collision_bound_20261115
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    (P {ω | (2 : ℝ) ≤ (N ω).toReal}).toReal ≤ r ^ 2 / 2 := by sorry
