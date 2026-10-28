-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_measure_compact_negative_band_small_time
-- name    : AvramDividend.Classical.levy_measure_compact_negative_band_small_time
-- status  : Open
-- author  : @WillR
-- created : 2026-10-27T11:58:07.569314+00:00
-- url     : https://prove2.me/theorems/540e2a63-e12e-4d40-a029-dc6b8ef1137d
-- title:
--   Small-time negative increment law recovers Levy mass on continuity bands
-- statement:
--   For a spectrally negative Levy model, the probability that the increment at time t lies in a compact interval strictly below zero, divided by t, converges to the Levy measure of that interval as t decreases to zero, provided the interval endpoints carry no Levy mass. This recovers finite-band jump intensity from the exact process law and supplies the analytic input for the zero-barrier early-downward-jump argument.
-- source:
--   Exact mathematical prerequisite for AvramDividend.Classical.ae_early_downward_jumps_of_infinite_negative_activity (ff758fb4-87e5-4eec-b153-b6135498ca04), on the path to barrier_zero_boundary_value (9e8e88ea-7f12-4d95-a4d1-a54abfee9305) and barrier_strategy_value (5eb63c8f-c2ca-45bb-8a39-04e9d0d6b849). The formal model provides the one-sided Laplace transform with its Levy-Khintchine exponent. The proof route analytically continues it to the characteristic function, applies Fourier inversion to smooth compactly supported tests away from zero, and approximates the compact-band indicator from inside and outside at atomless endpoints. This declaration isolates the small-time vague-convergence step; it does not itself establish pathwise jump-count laws or the parent implication.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_measure_compact_negative_band_small_time
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ) (hab : a < b) (hb : b < 0)
    (ha0 : X.ν {a} = 0) (hb0 : X.ν {b} = 0) :
    Tendsto
      (fun t : ℝ≥0 =>
        P {ω | X.X t ω ∈ Icc a b} / ENNReal.ofReal (t : ℝ))
      (nhdsWithin (0 : ℝ≥0) (Ioi 0))
      (nhds (X.ν (Icc a b))) := by sorry
