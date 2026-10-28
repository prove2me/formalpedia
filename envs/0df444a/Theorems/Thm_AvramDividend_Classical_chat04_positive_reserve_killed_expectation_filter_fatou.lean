-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_killed_expectation_filter_fatou
-- name    : AvramDividend.Classical.chat04_positive_reserve_killed_expectation_filter_fatou
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:29:30.471852+00:00
-- url     : https://prove2.me/theorems/618ce98c-6c18-4093-8c09-b5d7243e7bfd
-- title:
--   Full-filter Fatou lower bound for killed q-scale expectations at time zero
-- statement:
--   For positive initial reserve, the liminf over the entire neighbourhood filter at time zero of the true history-killed discounted q-scale expectation dominates the initial q-scale value. The existing sequence form is a corollary, and this stronger result gives the lower semicontinuity half of the killed semigroup at zero.
-- source:
--   Exact import chain: Proved pathwise initial limit 55db0a3f and measurable killed payoff 2603b26a, with pinned Mathlib Fatou theorem lintegral_liminf_le. Direct analytic prerequisite to open killed renewal identity a885f0b3 and unbounded stopped two-sided exit aed50a34.

import Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_killed_scale_tendsto_initial
import Theorems.Thm_AvramDividend_Classical_chat04_killed_ennreal_scale_payoff_measurable
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_positive_reserve_killed_expectation_filter_fatou
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 < x) :
    ENNReal.ofReal (W x) ≤
      Filter.liminf (fun t : ℝ≥0 => ∫⁻ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P)
        (𝓝 0) := by sorry
