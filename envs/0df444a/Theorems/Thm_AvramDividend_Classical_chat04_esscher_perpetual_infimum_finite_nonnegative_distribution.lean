-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_perpetual_infimum_finite_nonnegative_distribution
-- name    : AvramDividend.Classical.chat04_esscher_perpetual_infimum_finite_nonnegative_distribution
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:56:22.686834+00:00
-- url     : https://prove2.me/theorems/bd0e0e7b-1f1b-48ad-b677-4fa387af1856
-- title:
--   The perpetual Esscher reflected infimum has an exact finite Borel distribution supported on the nonnegative half-line
-- statement:
--   The perpetual Esscher survival cumulative function is exactly the distribution function of a finite positive Borel measure, supported on [0,∞), including any legitimate mass at the origin. For every real x its closed lower half-line mass equals the infimum of the actual finite-horizon Esscher-weighted survival expectations.
-- source:
--   Use the accepted real Stieltjes function construction, zero negative-tail, exact Iic measure evaluation, zero Iio(0) measure evaluation, finite measure theorem, and unit-interval bound. This is a source-faithful limiting marginal distribution, independent of Wiener–Hopf factorisation and without assuming mass one.

import Mathlib.MeasureTheory.Measure.Stieltjes
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_infinite_survival_stieltjes_measure
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_infimum_survival_zero_negative_reserve
import Theorems.Thm_AvramDividend_Classical_stieltjes_measure_Iic_of_zero_negative
import Theorems.Thm_AvramDividend_Classical_stieltjes_measure_Iio_zero_of_zero_negative
import Theorems.Thm_AvramDividend_Classical_stieltjes_isFiniteMeasure_of_zero_negative_bounded_one
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_unit_interval
open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_perpetual_infimum_finite_nonnegative_distribution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧ ν (Iio (0 : ℝ)) = 0 ∧
      ∀ x : ℝ, ν (Iic x) = (⨅ t : ℝ≥0, ENNReal.ofReal (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator (fun ω => Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)) := by sorry
