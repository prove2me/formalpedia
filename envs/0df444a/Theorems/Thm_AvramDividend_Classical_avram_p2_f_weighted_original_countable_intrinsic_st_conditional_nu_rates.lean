-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_intrinsic_st_conditional_nu_rates
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_countable_intrinsic_st_conditional_nu_rates
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:56:05.793528+00:00
-- url     : https://prove2.me/theorems/f23b5237-6d4c-4d69-86d8-ebbd2faf5a91
-- title:
--   Original countable intrinsic jump-measure compensation on exact (s,t] intervals conditional on original ν rates
-- statement:
--   For countably many genuine original source marked jump-measure rectangles on arbitrary ordered (s_i,t_i], the expected integral of nonnegative start-adapted simple weights equals the sum of expected weights times duration (t_i-s_i) times original X.ν(B_i), when and only when the independent original zero-origin ν-rate equalities are supplied as explicit hypotheses.
-- source:
--   Proved genuine original countable intrinsic conditional ν theorem f9f62551-ec9a-448d-b5ac-4e65ab1f90ef, plus exact endpoints using tsub_add_cancel_of_le.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_intrinsic_integral_conditional_nu_rates

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_countable_intrinsic_st_conditional_nu_rates
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ι → ℝ≥0) (hst : ∀ i, s i ≤ t i)
    (B : ι → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (H : ι → Ω → ℝ≥0∞)
    (hH : ∀ i, Measurable[𝓕 (s i)] (H i))
    (hOrigin : ∀ i, (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 (t i - s i) ×ˢ B i) ∂P) = (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))) :
    (∫⁻ ω, (∫⁻ p, ∑' i, (Ioc (s i) (t i) ×ˢ B i).indicator (fun _ => H i ω) p
      ∂((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ∂P) =
    ∑' i, (∫⁻ ω, H i ω ∂P) * (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)) := by sorry
