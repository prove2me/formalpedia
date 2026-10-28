-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_eq_densePrefix_with_endpoint
-- name    : AvramDividend.Classical.runningSup_eq_densePrefix_with_endpoint
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T11:27:07.406798+00:00
-- url     : https://prove2.me/theorems/7a9fc512-1c2c-4c18-9c8b-b9223bb874a1
-- title:
--   Actual Lévy running supremum recovered from dense observations and the terminal time
-- statement:
--   For each spectrally negative Lévy sample path, any dense observation set containing time zero recovers the true running supremum at each finite horizon once the horizon endpoint is included. This connects the continuous Stieltjes dividend regulator with the countable path-space sampling functional used in strong-Markov valuation, without assuming left continuity at the endpoint.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1. Reuse proved runningSup_eq_rawSup_nonneg, dense_timeSup_with_endpoint, levyPath_bddAbove_Icc.

import Mathlib.Topology.Order
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Theorems.Thm_AvramDividend_Classical_dense_timeSup_with_endpoint
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_eq_densePrefix_with_endpoint
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Set ℝ≥0) (hDense : Dense S) (h0 : (0 : ℝ≥0) ∈ S)
    (t : ℝ≥0) (ω : Ω) :
    runningSup X t ω =
      max (⨆ s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t}, X.X s.1 ω)
        (X.X t ω) := by
  sorry
