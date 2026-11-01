-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_intrinsic_disjoint_negative_void_intervals_independent
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_disjoint_negative_void_intervals_independent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:10:09.306607+00:00
-- url     : https://prove2.me/theorems/055c57b5-c22b-4c34-97f6-4b00d17f45dd
-- title:
--   Intrinsic original Lévy negative jump-counting measure has independent voids in ordered disjoint intervals
-- statement:
--   Let the literal original-source marked counting measure be count restricted to actual positive nonzero X jumps and mapped to the original (time, jump mark) graph. Under source BV and finite negative Lévy intensity, its two void events on disjoint ordered intervals (s,t]×(-∞,0) and (u,v]×(-∞,0), s≤t≤u≤v, are independent. Pathwise source intrinsic count zero iff no original jump and true-original-space disjoint void independence imply the factorization. The source is never replaced by a newly constructed Poisson model. This is a finite-dimensional void-count independence, not the full Poisson count or predictable compensator.
-- source:
--   Canonically Proved all-sample original intrinsic rectangle zero-event provider 4087af7c; the separately submitted source disjoint nojump independent provider must be canonically Proved before proof submission. The exact same original Ω, P, source X.X paths, ν and right-continuous original filtration are preserved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_disjoint_negative_void_intervals_independent
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t u v : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v) :
    P ({ω : Ω |
      ((Measure.count.restrict {r : ℝ≥0 |
        0 < r ∧ X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r ≠ 0}).map
        (fun r : ℝ≥0 => (r,
          X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r)))
        (Ioc s t ×ˢ Iio (0 : ℝ)) = 0} ∩
       {ω : Ω |
        ((Measure.count.restrict {r : ℝ≥0 |
          0 < r ∧ X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r ≠ 0}).map
          (fun r : ℝ≥0 => (r,
            X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r)))
          (Ioc u v ×ˢ Iio (0 : ℝ)) = 0}) =
      P {ω : Ω |
        ((Measure.count.restrict {r : ℝ≥0 |
          0 < r ∧ X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r ≠ 0}).map
          (fun r : ℝ≥0 => (r,
            X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r)))
          (Ioc s t ×ˢ Iio (0 : ℝ)) = 0} *
      P {ω : Ω |
        ((Measure.count.restrict {r : ℝ≥0 |
          0 < r ∧ X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r ≠ 0}).map
          (fun r : ℝ≥0 => (r,
            X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r)))
          (Ioc u v ×ˢ Iio (0 : ℝ)) = 0} := by sorry
