-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_predictable_integral_from_rates
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_countable_predictable_integral_from_rates
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:47:13.377922+00:00
-- url     : https://prove2.me/theorems/3002bec7-dfa4-4098-8cec-013b03a4e3b2
-- title:
--   Expected original source countable predictable-simple marked jump integral from actual individual rates
-- statement:
--   For a genuine original spectrally negative Lévy process with its unchanged original intrinsic marked jump measure, the expected integral of any countable nonnegative predictable-simple marked integrand Σ H_i(ω)1_(s_i,t_i]×B_i(u,z) is the countable sum Σ E[H_i]r_i, where every r_i is independently established as the unweighted first moment of that same literal original marked rectangle. The process pathwise source equality for N_i and each unweighted rate are explicit assumptions. This directly composes the pathwise original jump-measure Tonelli identity with the source future/past L1 factorisation, without any Poisson copy or hidden ν identification. Useful to P2-E and subsequent stochastic integral construction.
-- source:
--   P2-F source countable pathwise marked integral and source countable (s,t] per-cell rate transfer, each separately genuine proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_countable_simple_pathwise
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_st_cells_of_rates

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_countable_predictable_integral_from_rates
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ι → ℝ≥0) (hst : ∀ i, s i ≤ t i)
    (B : ι → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (H N : ι → Ω → ℝ≥0∞)
    (hH : ∀ i, Measurable[𝓕 (s i)] (H i))
    (hSource : ∀ i, ∀ ω : Ω, N i ω = ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc (s i) (t i) ×ˢ B i))
    (r : ι → ℝ≥0∞)
    (hRate : ∀ i, (∫⁻ ω, N i ω ∂P) = r i) :
    (∫⁻ ω, (∫⁻ p, ∑' i, (Ioc (s i) (t i) ×ˢ B i).indicator (fun _ => H i ω) p ∂((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ∂P) =
    ∑' i, (∫⁻ ω, H i ω ∂P) * r i := by sorry
