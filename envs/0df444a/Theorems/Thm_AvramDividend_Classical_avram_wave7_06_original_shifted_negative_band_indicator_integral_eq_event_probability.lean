-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_shifted_negative_band_indicator_integral_eq_event_probability
-- name    : AvramDividend.Classical.avram_wave7_06_original_shifted_negative_band_indicator_integral_eq_event_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:42:44.458427+00:00
-- url     : https://prove2.me/theorems/14ee2bc3-0ee3-4222-81c9-10c6e189c20f
-- title:
--   Original shifted negative-band occupied indicator integral equals its actual event probability
-- statement:
--   For the exact same Ω, P and spectrally negative Lévy X, the nonzero genuine negative marked jump count event E on (s,s+T] is measurable, and the lintegral of its 0/1 indicator equals P(E). Source original Borel marked-void measurability is the only imported proof fact; no Poisson or source rate premise.
-- source:
--   Wave7-06 direct source marked occupied indicator expectation decomposition. Bridges exact source cell measurability to the finite-grid mean and avoids dependency on the full source stationary occupied-cell theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_shifted_negative_band_indicator_integral_eq_event_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (n : ℕ) :
    (let E : Set Ω := {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) ≠ 0}
     (∫⁻ ω, E.indicator (fun _ => (1 : ENNReal)) ω ∂P) = P E) := by sorry
