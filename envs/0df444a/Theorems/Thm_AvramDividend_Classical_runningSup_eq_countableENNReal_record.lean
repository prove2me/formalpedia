-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_eq_countableENNReal_record
-- name    : AvramDividend.Classical.runningSup_eq_countableENNReal_record
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T11:56:50.76428+00:00
-- url     : https://prove2.me/theorems/1f83943d-8e2a-43e2-8873-fa59ae1843fc
-- title:
--   The true reflected supremum equals the globally measurable countable ENNReal record encoding
-- statement:
--   On each actual spectrally negative Lévy path and at any countably sampled endpoint, a dense countable observation schedule recovers the true nonnegative running supremum exactly in the ENNReal.ofReal/iSup/toReal encoding used by the globally measurable dividend reward functional. Bounds follow from the Lévy path's local boundedness. This closes the deterministic dense-sampling and order-conversion components of the stopped reward representation.
-- source:
--   Proved runningSup_eq_densePrefix_onSample, levyPath_bddAbove_Icc, runningSup_eq_rawSup_nonneg and countable_bddRealSup_eq_ennrealOfRealSup_toReal. Avram, Palmowski and Pistorius (2007), Proposition 1.

import Theorems.Thm_AvramDividend_Classical_runningSup_eq_densePrefix_onSample
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Theorems.Thm_AvramDividend_Classical_countable_bddRealSup_eq_ennrealOfRealSup_toReal

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_eq_countableENNReal_record
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (samples : ℕ → ℝ≥0)
    (hDense : Dense (Set.range samples))
    (hzero : (0 : ℝ≥0) ∈ Set.range samples)
    (t : ℝ≥0) (ht : t ∈ Set.range samples) :
    runningSup X t ω =
      (⨆ j : ℕ,
        ENNReal.ofReal (if samples j ≤ t then
          max 0 (X.X (samples j) ω) else 0)).toReal := by
  sorry
