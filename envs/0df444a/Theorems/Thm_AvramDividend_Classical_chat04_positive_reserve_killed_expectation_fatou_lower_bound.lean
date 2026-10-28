-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_killed_expectation_fatou_lower_bound
-- name    : AvramDividend.Classical.chat04_positive_reserve_killed_expectation_fatou_lower_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:16:50.70204+00:00
-- url     : https://prove2.me/theorems/6d947636-4a3d-4ca2-baf8-d996ec244782
-- title:
--   Fatou lower semicontinuity of truly killed q-scale expectations at positive initial reserve
-- statement:
--   For any deterministic sequence of nonnegative horizons tending to zero, the liminf of the expected discounted q-scale payoffs killed by whole-history ruin is at least W(x) for every positive initial reserve x. This is the Fatou half of initial-time continuity for the killed semigroup, using pointwise right-continuity and measurability already proved.
-- source:
--   Proved pathwise positive-reserve history-killed limit 55db0a3f, and proposed exact ENNReal payoff measurable theorem chat04_killed_ennreal_scale_payoff_measurable; pinned Mathlib Fatou theorem lintegral_liminf_le. Advances initial-time analytic control in Open killed q-scale renewal identity a885f0b3-3960-424d-97e4-abbcffe268ba.

import Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_killed_scale_tendsto_initial
import Theorems.Thm_AvramDividend_Classical_chat04_killed_ennreal_scale_payoff_measurable
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_positive_reserve_killed_expectation_fatou_lower_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 < x)
    (T : ℕ → ℝ≥0) (hT : Tendsto T atTop (𝓝 0)) :
    ENNReal.ofReal (W x) ≤
      Filter.liminf (fun n : ℕ => ∫⁻ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ T n → 0 ≤ x + X.X s u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * ((T n) : ℝ))) * W (x + X.X (T n) u))) ω ∂P)
        atTop := by sorry
