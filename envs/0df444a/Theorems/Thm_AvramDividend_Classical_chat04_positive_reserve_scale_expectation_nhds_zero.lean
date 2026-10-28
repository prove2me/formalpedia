-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_scale_expectation_nhds_zero
-- name    : AvramDividend.Classical.chat04_positive_reserve_scale_expectation_nhds_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:22:04.222043+00:00
-- url     : https://prove2.me/theorems/7aa17ffd-16b1-47cd-8950-ebb51ef628ae
-- title:
--   Full-neighbourhood initial continuity of expected q-scale rewards
-- statement:
--   At positive starting reserve and with a nonnegative discount admitting a positive Lévy Laplace gap, the expectation of the discounted q-scale reward converges to W(x) along the full neighbourhood filter of time zero. Every convergent deterministic time sequence has a bounded range, so the accepted bounded-sequence L² expectation-convergence theorem applies. First countability upgrades convergence along every sequence to full filter convergence, the analytic starting-time input for the killed semigroup harmonicity needed in strict two-sided exit.
-- source:
--   Direct import of accepted bounded deterministic sequence expectation theorem e89e3760 and pinned Mathlib Filter.tendsto_iff_seq_tendsto, Filter.Tendsto.bddAbove_range. Supports terminal-only time-zero q-scale convergence, accepted killed Fatou/limsup bridges 618ce98c and 089d8e8d, then Open killed harmonicity a885f0b3 and stopped exit 09663d0d.

import Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_deterministic_scale_expectation_tendsto
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Topology.Order.LiminfLimsup

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.chat04_positive_reserve_scale_expectation_nhds_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ) (hx : 0 < x) :
    Filter.Tendsto
      (fun t : ℝ≥0 => ∫ ω,
        Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω) ∂P)
      (𝓝 0) (𝓝 (W x)) := by sorry
