-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_positive_clock_centered_integral_of_zero_complement
-- name    : AvramDividend.Classical.avram_p4_f4_positive_clock_centered_integral_of_zero_complement
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:29:33.080755+00:00
-- url     : https://prove2.me/theorems/44fbfa37-c9f4-41f6-a38b-24bbc6f2753f
-- title:
--   Centred original stochastic source remains centred on the positive clock when it vanishes at time zero
-- statement:
--   A source martingale increment with zero global mean and zero pathwise value on the zero-clock event has zero integral restricted to the strictly positive stopping event. This elementary reusable signed measure fact is an independent bridge in the mixed Gaussian-jump all-cap positive-clock source proof.
-- source:
--   Exact integral_indicator reduction under the provided measurability of the event; no stochastic process or cap assumption and no circular reference to the target theorem.

import Mathlib.MeasureTheory.Integral.Bochner.Set
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_positive_clock_centered_integral_of_zero_complement
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : Set Ω) (hS : MeasurableSet S) (M : Ω → ℝ)
    (hMean : (∫ ω, M ω ∂P) = 0)
    (hZeroOutside : ∀ᵐ ω ∂P, ω ∉ S → M ω = 0) :
    (∫ ω in S, M ω ∂P) = 0 := by sorry
