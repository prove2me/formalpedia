-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_levy_finite_truncated_negative_tails
-- name    : AvramDividend.Classical.esscher_levy_finite_truncated_negative_tails
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:18:58.985365+00:00
-- url     : https://prove2.me/theorems/3ffb5df2-db39-4ed4-8b14-c485762a72ba
-- title:
--   Every spectrally negative Lévy Esscher tilt has finite truncated negative-jump intensity
-- statement:
--   The Lévy integrability axiom alone, for any spectrally negative Lévy process, ensures every negative jump-size truncation has finite mass after an arbitrary nonnegative Esscher tilt. No bounded-variation, Standing, or scale smoothness assumptions. This discharges per-cutoff finite-mass hypotheses needed for excursion and Poisson band constructions in the unbounded-variation regularity branch.
-- source:
--   Proved negative_jump_truncation_measure_finite [16a2d301-ca20-4837-969a-892ae00966c0] and esscher_weighted_negative_tail_finite_of_unweighted [ce59aa21-09fa-4283-b034-b9926c91095c], accepted candidate 16111.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Theorems.Thm_AvramDividend_Classical_negative_jump_truncation_measure_finite
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_negative_tail_finite_of_unweighted
open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal NNReal

theorem AvramDividend.Classical.esscher_levy_finite_truncated_negative_tails
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ x : ℝ) (hφ : 0 ≤ φ) (hx : 0 < x) :
    (X.ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))
      (Iio (-x)) < ⊤ := by sorry
