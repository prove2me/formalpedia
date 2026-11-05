-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_h_original_BV_positive_interior_has_concrete_Lipschitz_band
-- name    : AvramDividend.Classical.avram_p3_h_original_BV_positive_interior_has_concrete_Lipschitz_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:00:10.71006+00:00
-- url     : https://prove2.me/theorems/57f9bd71-01d0-47e1-8339-09ac80bb9e4b
-- title:
--   Original BV strict interior automatically yields concrete stopped-compensator compact Lipschitz constants
-- statement:
--   For the original bounded-variation spectrally negative Lévy process and any interior reserve state, automatically construct a compact admissible reserve band and explicit nonnegative local Lipschitz and lower-state value constants. This is the source-facing localisation interface for the original P3-E/G stopped jump compensator.
-- source:
--   Proved P3-G compact Lipschitz 0990d837, Proved cap openness b917eaf2, original compact geometry bridge 5ae2944f.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_h_localise_compact_band_at_interior
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_source_BV_C1_compact_Lipschitz_value_bounds
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ubv_strict_C2_interior_isOpen
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_h_original_BV_positive_interior_has_concrete_Lipschitz_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwCont : ContinuousOn w (Ici 0))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (z : ℝ) (hz : 0 < z) (hzC : ENNReal.ofReal z < C) :
    ∃ a b L R : ℝ, 0 < a ∧ a ≤ 2 ∧ a ≤ b ∧ z ∈ Icc a b ∧
      0 ≤ L ∧ 0 ≤ R ∧
      (∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
        |w u - w v| ≤ L * |u - v|) ∧
      (∀ v : ℝ, v ≤ b → |w v| ≤ R) := by sorry
