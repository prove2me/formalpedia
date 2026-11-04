-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_st_cells_of_rates
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_countable_st_cells_of_rates
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:22:56.34367+00:00
-- url     : https://prove2.me/theorems/f35c0661-c8d6-4670-bf42-64bb284856c9
-- title:
--   Countably many genuine original intrinsic (s,t] predictable marked rectangles compensate from source rates
-- statement:
--   A countable family of actual original-process marked rectangles (s_i,t_i] × B_i, with s_i≤t_i and possibly varying adapted past weights H_i, satisfies expected infinite predictable-cell compensation from the separately proved unweighted count means of those actual rectangles. This uses the precise deterministic (s,t] time convention of P2-E's compensator. Each equality of N_i with original intrinsic jump count, each mark measurability and every unweighted rate is an explicit premise. The conclusion follows from source original future-past factorisation and Tonelli, without Poisson substitution or assuming a ν formula.
-- source:
--   Original Proved 267e2229, d9c55240; pinned Mathlib add_tsub_cancel_left and lintegral_tsum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_future_past_product

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_countable_st_cells_of_rates
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
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i))
    (r : ι → ℝ≥0∞)
    (hRate : ∀ i, (∫⁻ ω, N i ω ∂P) = r i) :
    (∫⁻ ω, ∑' i, H i ω * N i ω ∂P) =
    ∑' i, (∫⁻ ω, H i ω ∂P) * r i := by sorry
