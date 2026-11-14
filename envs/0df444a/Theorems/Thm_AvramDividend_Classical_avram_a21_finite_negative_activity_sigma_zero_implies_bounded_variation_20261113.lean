-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_finite_negative_activity_sigma_zero_implies_bounded_variation_20261113
-- name    : AvramDividend.Classical.avram_a21_finite_negative_activity_sigma_zero_implies_bounded_variation_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:33:47.851698+00:00
-- url     : https://prove2.me/theorems/9827a243-66be-4227-a76a-3470c95e5e44
-- title:
--   Finite original negative Levy activity with zero Gaussian coefficient implies bounded variation
-- statement:
--   Under finite original negative mark activity, if the Gaussian coefficient vanishes then X satisfies the source bounded-variation condition. The negative mark absolute weight is at most one on (-1,0), and the negative mark Levy measure is finite. Apply pinned Mathlib setLIntegral_lt_top_of_le_nnreal.
-- source:
--   Exact source BoundedVariation definition sigma zero and small-negative absolute Levy moment, pinned setLIntegral_lt_top_of_le_nnreal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_finite_negative_activity_sigma_zero_implies_bounded_variation_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hσ : X.σ = 0) :
    X.BoundedVariation := by sorry
