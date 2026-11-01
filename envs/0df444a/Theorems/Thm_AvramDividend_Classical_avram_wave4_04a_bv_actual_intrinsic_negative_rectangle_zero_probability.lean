-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_intrinsic_negative_rectangle_zero_probability
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_negative_rectangle_zero_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:57:35.838729+00:00
-- url     : https://prove2.me/theorems/3577dff9-8d71-4bdb-aa7f-f6d58b934fc5
-- title:
--   Genuine original BV Lévy intrinsic negative counting measure has Poisson zero-count probability
-- statement:
--   For an actual finite-activity bounded-variation source spectrally negative Lévy X on its own probability space, the intrinsic original-path counting measure of (s,t]×(-∞,0) is zero with exactly exp(-(t-s)ν((−∞,0))) probability. This directly states a Poisson zero-count law for the original marked counting measure, not an equal-law Lévy replacement. It does not assert the full Poisson distribution, disjoint-band independence or predictable compensation.
-- source:
--   Original intrinsic rectangle count f6336d40, original nonpositive jump mark e95fe5bc, and new pathwise zero-count equivalence and source no-jump exponential theorem once canonically Proved. Set ext on every sample identifies literal count-zero event with no-jump event; apply source probability. The formal statement itself needs only the source definition and Mathlib.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_negative_rectangle_zero_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t) :
    P.real {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iio (0 : ℝ)) = 0} =
      Real.exp (-(((t - s : ℝ≥0) : ℝ) *
        (X.ν (Iio (0 : ℝ))).toReal)) := by sorry
