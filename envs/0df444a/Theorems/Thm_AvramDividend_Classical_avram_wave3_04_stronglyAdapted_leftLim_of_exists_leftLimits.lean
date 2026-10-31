-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_stronglyAdapted_leftLim_of_exists_leftLimits
-- name    : AvramDividend.Classical.avram_wave3_04_stronglyAdapted_leftLim_of_exists_leftLimits
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T12:31:57.408683+00:00
-- url     : https://prove2.me/theorems/4a78651d-055e-4df8-a3d2-237dd30e6889
-- title:
--   Strong adaptedness of the left-limit modification of a genuinely adapted process
-- statement:
--   If a process Z on nonnegative time is strongly adapted to a specified filtration and has a finite strict-left limit at every positive time on every path, its left-limit modification remains strongly adapted to the same filtration. At positive times a countable deterministic strict-past approximation has a strongly measurable limit at the current filtration; that value equals Function.leftLim. At zero Function.leftLim agrees with the original Z value. No usual-filtration enlargement or semimartingale assumptions are introduced.
-- source:
--   Pinned Mathlib StronglyMeasurable.limUnder, leftLim_eq_of_isBot, leftLim_eq_of_tendsto and nhdsLT_neBot_of_exists_lt. An exact private remote probe d5422d52-d122-467b-a12e-d31ecf3e0104 reached the compiler sentinel without candidate errors, source SHA-256 baa8c682ef875eaef7786529439ce42d34400e4134ae025b355fbda3ce81d09f.

import Mathlib

open Filter Set Topology MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.avram_wave3_04_stronglyAdapted_leftLim_of_exists_leftLimits
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Z : ℝ≥0 → Ω → ℝ)
    (hZ : StronglyAdapted 𝓕 Z)
    (hleft : ∀ ω (t : ℝ≥0), 0 < t →
      ∃ l : ℝ, Filter.Tendsto (fun s => Z s ω)
        (nhdsWithin t (Set.Iio t)) (nhds l)) :
    StronglyAdapted 𝓕
      (fun t ω => Function.leftLim (fun s => Z s ω) t) := by sorry
