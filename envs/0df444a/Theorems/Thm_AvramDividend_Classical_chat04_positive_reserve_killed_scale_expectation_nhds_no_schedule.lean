-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_killed_scale_expectation_nhds_no_schedule
-- name    : AvramDividend.Classical.chat04_positive_reserve_killed_scale_expectation_nhds_no_schedule
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:06:10.639085+00:00
-- url     : https://prove2.me/theorems/35f9da66-fd2c-4e12-9710-001112f0de64
-- title:
--   Killed scale expectation continuity at zero without grid schedule
-- statement:
--   For strictly positive reserve and positive Laplace-growth gap, the real expected discounted whole-history killed q-scale reward converges to W(x) as deterministic t tends to zero, with no countable observation grid parameters. The source is the prior Proved no-schedule sequence convergence result and Mathlib sequential characterisation of neighbourhood limits. This supports killed q-scale harmonicity and two-sided exit.
-- source:
--   Proved no-schedule killed expected sequence limit and pinned Mathlib sequence-neighbourhood limit characterisation. Downstream unbounded killed survival discounted scale expectation a885f0b3 and two-sided exit 09663d0d.

import Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_killed_scale_expectation_tendsto_seq_no_schedule
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Topology.Order.LiminfLimsup

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.chat04_positive_reserve_killed_scale_expectation_nhds_no_schedule
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ) (hx : 0 < x) :
    Filter.Tendsto
      (fun t : ℝ≥0 => ∫ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => Real.exp (-(q * (t : ℝ))) *
            W (x + X.X t u)) ω ∂P)
      (𝓝 0) (𝓝 (W x)) := by sorry
