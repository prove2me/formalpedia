-- Prove2me | Theorems.Thm_AvramDividend_Classical_one_sided_lintegral_le_of_grid_tendsto
-- name    : AvramDividend.Classical.one_sided_lintegral_le_of_grid_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T06:57:26.110359+00:00
-- url     : https://prove2.me/theorems/4d3fbbbc-4aaf-4b0c-bc31-9a86286d3af1
-- title:
--   Nonnegative grid expectation upper bounds survive pointwise time-mesh convergence
-- statement:
--   For an arbitrary measure space and measurable ENNReal-valued functions f_n, suppose f_n(ω) converges to g(ω) for every sample ω. If the Lebesgue integrals of every f_n are bounded by the same extended-nonnegative number B, then the integral of g is also bounded by B. Prove this using the pinned Mathlib Fatou inequality lintegral_liminf_le, equality of liminf with a true pointwise limit, and the uniform eventual upper bound of the integral sequence. This reusable lemma needs no probability-mass or domination assumption and will close the analytic final step of one-sided Lévy first-passage bounds.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Order.LiminfLimsup
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped ENNReal

theorem AvramDividend.Classical.one_sided_lintegral_le_of_grid_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (f : ℕ → Ω → ℝ≥0∞) (g : Ω → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n))
    (hlim : ∀ ω, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (B : ℝ≥0∞)
    (hB : ∀ n, (∫⁻ ω, f n ω ∂P) ≤ B) :
    (∫⁻ ω, g ω ∂P) ≤ B := by sorry
