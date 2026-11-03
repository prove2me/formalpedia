-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_actual_source_negative_increment_exponential_fourth_tail_bound
-- name    : AvramDividend.Classical.avram_wave7_01_actual_source_negative_increment_exponential_fourth_tail_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:41:18.322324+00:00
-- url     : https://prove2.me/theorems/1d1be1d3-184e-4fa0-b52d-24a9a2ac40bb
-- title:
--   Original Lévy negative increment tail bounded by its fourth exponential jump-deficit moment
-- statement:
--   For the actual original SpectrallyNegativeLevy X and original P, an event that its genuine increment at h is at most −ε forces its positive fourth exponential deficit to exceed the explicit threshold (1−exp(−θε))⁴. The exact pinned Mathlib Markov inequality converts this deterministic bound into an original-process ENNReal probability bound by its original fourth moment. Pointwise measurability of the source increment is explicit. This connects the Proved original small-time fourth exponential derivative e6973988 to negative jump tail probability control without introducing an independent Poisson/Brownian model.
-- source:
--   Pinned Mathlib MeasureTheory.mul_meas_ge_le_lintegral verified remote signature 55539671; original smalltime fourth moment e6973988

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_actual_source_negative_increment_exponential_fourth_tail_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (h : ℝ≥0) (ε θ : ℝ) (hε : 0 < ε) (hθ : 0 < θ)
    (hXm : Measurable (X.X h)) :
    (ENNReal.ofReal ((1 - Real.exp (-θ * ε)) ^ 4)) *
      P {ω : Ω | X.X h ω ≤ -ε} ≤
    (∫⁻ ω, ENNReal.ofReal
      ((Real.exp (θ * X.X h ω) - 1) ^ 4) ∂P) := by sorry
