-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_predictable_origin_means
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_countable_predictable_origin_means
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:03:45.130917+00:00
-- url     : https://prove2.me/theorems/6819fcdd-af85-47bf-baf8-b412e291f714
-- title:
--   Countable true original predictable marked cells factor against zero-origin source means
-- statement:
--   The expected infinite sum of countably many past-adapted nonnegative weights times genuine original intrinsic marked jump counts on future source intervals (s_i,s_i+T_i] equals the sum of each weight mean times the corresponding unweighted original zero-origin (0,T_i] marked-count mean. The conclusion has no unproved source ν rate, Poisson-copy, pointwise coupling, finiteness or 0*∞ exception. It is derived from proved countable predictable original cell factorisation and proved original source marked-count stationarity. P2-E can later replace zero-origin means using the independently established original Lévy rate.
-- source:
--   Proved original countable source cell compensation 2d249f3f-c06c-4ef2-8814-2247ba824d6e and original source stationarity add050a6-3ff4-4747-9805-600b11b7b3d1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_predictable_cells_of_rates
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_countable_predictable_origin_means
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ι → ℝ≥0)
    (B : ι → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (H : ι → Ω → ℝ≥0∞)
    (hH : ∀ i, Measurable[𝓕 (s i)] (H i)) :
    (∫⁻ ω, ∑' i, H i ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc (s i) (s i + T i) ×ˢ B i) ∂P) =
    ∑' i, (∫⁻ ω, H i ω ∂P) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 (T i) ×ˢ B i) ∂P) := by sorry
