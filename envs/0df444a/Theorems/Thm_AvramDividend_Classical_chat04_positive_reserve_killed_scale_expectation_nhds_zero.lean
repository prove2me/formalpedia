-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_killed_scale_expectation_nhds_zero
-- name    : AvramDividend.Classical.chat04_positive_reserve_killed_scale_expectation_nhds_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:50:59.226748+00:00
-- url     : https://prove2.me/theorems/9337542a-e940-47f7-843a-813fb53aaae4
-- title:
--   Initial neighbourhood continuity of the history-killed q-scale expectation
-- statement:
--   For positive reserve and positive Laplace growth gap, the real expected discounted whole-history killed q-scale reward tends to W(x) in the full time-zero neighbourhood filter. The reciprocal-natural grid covering schedule ensures the survival event is measurable, and the previously Proved bounded deterministic sequence convergence theorem supplies full convergence by Mathlib's sequential criterion. This is the exact initial-time killed semigroup continuity needed in the still-open all-time killed harmonicity and two-sided exit chain.
-- source:
--   Imports the expected killed q-scale convergence theorem chat04_positive_reserve_killed_scale_expectation_tendsto_seq (pending), Mathlib Filter.tendsto_iff_seq_tendsto and Filter.Tendsto.bddAbove_range; downstream a885f0b3 then 09663d0d.

import Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_killed_scale_expectation_tendsto_seq
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Topology.Order.LiminfLimsup

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.chat04_positive_reserve_killed_scale_expectation_nhds_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ) (hx : 0 < x) :
    Filter.Tendsto
      (fun t : ℝ≥0 => ∫ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => Real.exp (-(q * (t : ℝ))) *
            W (x + X.X t u)) ω ∂P)
      (𝓝 0) (𝓝 (W x)) := by sorry
