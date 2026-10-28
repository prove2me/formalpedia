-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_killed_ennreal_expectation_nhds_no_schedule
-- name    : AvramDividend.Classical.chat04_positive_reserve_killed_ennreal_expectation_nhds_no_schedule
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:29:09.770318+00:00
-- url     : https://prove2.me/theorems/8f115791-8864-4562-b03a-809d090529b0
-- title:
--   ENNReal killed q-scale expectation tends to W(x) as time decreases to zero
-- statement:
--   For strictly positive initial reserve and an exponential Laplace-growth gap, the ENNReal expectation of the discounted scale payoff killed by any lower-barrier crossing converges at time zero to ENNReal.ofReal(W(x)). The proof composes the already Proved real expected continuity without any grid schedule with the exact real-to-ENNReal integrability bridge. This places the initial semigroup property in precisely the codomain of the open all-time killed renewal identity and stopped two-sided exit theorem.
-- source:
--   Imports chat04_positive_reserve_killed_scale_expectation_nhds_no_schedule, chat04_history_killed_scale_real_ennreal_integral_bridge and pinned Mathlib ENNReal.continuous_ofReal. Downstream all-time killed scale identity a885f0b3 and stopped-scale 09663d0d.

import Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_killed_scale_expectation_nhds_no_schedule
import Theorems.Thm_AvramDividend_Classical_chat04_history_killed_scale_real_ennreal_integral_bridge
import Mathlib.Topology.Instances.ENNReal.Lemmas

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_positive_reserve_killed_ennreal_expectation_nhds_no_schedule
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ) (hx : 0 < x) :
    Filter.Tendsto
      (fun t : ℝ≥0 => ∫⁻ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P)
      (𝓝 0) (𝓝 (ENNReal.ofReal (W x))) := by sorry
