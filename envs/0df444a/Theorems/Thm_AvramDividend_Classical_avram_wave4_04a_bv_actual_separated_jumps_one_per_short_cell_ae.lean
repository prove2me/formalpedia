-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_separated_jumps_one_per_short_cell_ae
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_separated_jumps_one_per_short_cell_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:10:22.044196+00:00
-- url     : https://prove2.me/theorems/90932671-54d3-48b0-863e-1eee9b61180b
-- title:
--   Actual BV Lévy jump times occupy at most one per sufficiently short original-time grid cell, uniformly almost surely
-- statement:
--   For every actual original-source BV finite-negative-activity spectrally negative Lévy X and finite T>0, on a single P-full event there is a random but positive mesh threshold δ(ω,T) such that every half-open grid cell of metric diameter below δ contains at most one distinct genuine nonzero original X jump time in (0,T]. This removes the at-most-one-per-cell hypothesis from the actual intrinsic N_X finite-grid occupancy bridge once a grid's cells are sufficiently short; no auxiliary process, Poisson law, random measure measurability or compensator is asserted.
-- source:
--   Canonically Proved original finite-activity BV source jump-time uniform separation 1edc0870-08fc-4455-91c9-6edc0702656e. If two distinct actual jump times lie in the same interval (a,b], their metric distance is at most dist(a,b); this contradicts the source uniform lower bound δ when cell width is strictly below δ. Uses the actual original Ω, ω, ΔX marks, P and finite-activity assumptions unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_separated_jumps_one_per_short_cell_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∃ δ : ℝ, 0 < δ ∧
      ∀ (n : ℕ) (grid : ℕ → ℝ≥0),
        (∀ i : ℕ, i < n →
          dist (grid i) (grid (i + 1)) < δ) →
        ∀ i : ℕ, i < n →
        ∀ u v : ℝ≥0,
        (u ≤ T ∧ 0 < u ∧
          X.X u ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) u ≠ 0) →
        (v ≤ T ∧ 0 < v ∧
          X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0) →
        u ∈ Ioc (grid i) (grid (i + 1)) →
        v ∈ Ioc (grid i) (grid (i + 1)) → u = v := by sorry
