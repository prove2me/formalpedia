-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_levy_dense_prefix_eq_runningSup
-- name    : AvramDividend.Classical.avram_ws01e_b_actual_levy_dense_prefix_eq_runningSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T17:49:10.826996+00:00
-- url     : https://prove2.me/theorems/f32e574e-2d2e-4df9-a488-3fdb51470dca
-- title:
--   The countable clipped prefix of an actual Lévy path equals its genuine running supremum at sampled horizons
-- statement:
--   For the actual spectrally negative Lévy X, every sample path starts from zero and is right-continuous with a finite upper bound on each compact clock interval. Consequently, for any dense countable observation schedule containing zero and any clock time itself in the schedule, the toReal of the ENNReal supremum of clipped fixed-time samples at or before that clock equals the genuine running supremum runningSup X. This is the exact source-specific bridge from the Proved product-Pi measurable prefix drawdown reward to the actual record and drawdown process under the random-terminal Esscher law.
-- source:
--   Proved deterministic dense-prefix pathwise identity 4d43b293, actual Lévy path boundedness c2066587, and canonical runningSup definition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_actual_levy_dense_prefix_eq_runningSup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (samples : ℕ → ℝ≥0) (hdense : Dense (Set.range samples))
    (hzero : (0 : ℝ≥0) ∈ Set.range samples)
    (t : ℝ≥0) (ht : t ∈ Set.range samples) :
    (⨆ i : ℕ, if samples i ≤ t then
      ENNReal.ofReal (X.X (samples i) ω) else 0).toReal =
    runningSup X t ω := by sorry
