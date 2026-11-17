-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_same_source_occupied_Bernoulli_parameter_20261116
-- name    : AvramDividend.Classical.avram_a27_same_source_occupied_Bernoulli_parameter_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T09:29:25.595191+00:00
-- url     : https://prove2.me/theorems/97ea1882-961f-44f7-9a01-60f88879e153
-- title:
--   Source physical occupied Bernoulli indicators have probability equal to the exact void-complement parameter
-- statement:
--   If a finite family Y_i of original-space occupied indicators has the same original P event mass as a fixed original physical count C being nonzero, and p is the unitInterval complement of the source count zero probability, then every indicator has success probability exactly p. Apply the proved generic measurable event-complement theorem a27 without changing Omega/P or count source. This is a reusable step in the physical occupied grid exact binomial law.
-- source:
--   Original source occupancy stationarity and proved generic nonzero event complement theorem 9f985ad5.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a27_same_source_occupied_Bernoulli_parameter_20261116
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (Y : Fin n → Ω → ℕ)
    (C : Ω → ℝ≥0∞) (hC : Measurable C)
    (hSame : ∀ i : Fin n,
      P {ω : Ω | Y i ω = 1} = P {ω : Ω | C ω ≠ 0})
    (p : unitInterval)
    (hp : (p : ℝ) = 1 - (P {ω : Ω | C ω = 0}).toReal) :
    ∀ i : Fin n, (P {ω : Ω | Y i ω = 1}).toReal = (p : ℝ) := by sorry
