-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_perpetual_infimum_distribution_measure
-- name    : AvramDividend.Classical.chat04_esscher_perpetual_infimum_distribution_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:38:03.852167+00:00
-- url     : https://prove2.me/theorems/272f9635-c2f5-4c5e-8a3d-2ccaf9c43255
-- title:
--   The infinite-horizon Esscher survival function is exactly the cumulative law of a Borel measure
-- statement:
--   Construct a genuine Borel measure on the real line whose measure of each lower half-line up to x equals exactly the ENNReal-valued perpetual Esscher-weighted probability of survival from reserve x, defined as an infimum over all finite horizons. The measure is possibly defective, not assumed a probability measure. This is the rigorous descending running-infimum limiting law.
-- source:
--   Use Proved infinite-horizon Stieltjes function construction, Proved vanishing for negative starting reserves, generic Stieltjes half-line evaluation from the zero-left-tail condition, and Proved unit upper bounds to eliminate ENNReal infinity. The result makes no circular use of the root scale identity or the Wiener–Hopf scalar transform.

import Mathlib.MeasureTheory.Measure.Stieltjes
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_infinite_survival_stieltjes_measure
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_infimum_survival_zero_negative_reserve
import Theorems.Thm_AvramDividend_Classical_stieltjes_measure_Iic_of_zero_negative
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_unit_interval
open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_perpetual_infimum_distribution_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∃ ν : Measure ℝ, ∀ x : ℝ, ν (Iic x) = (⨅ t : ℝ≥0, ENNReal.ofReal (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator (fun ω => Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)) := by sorry
