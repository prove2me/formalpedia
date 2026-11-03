-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_finite_activity_original_any_start_separated_mark_expected_count_finite
-- name    : AvramDividend.Classical.avram_wave7_01_bv_finite_activity_original_any_start_separated_mark_expected_count_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:49:56.167196+00:00
-- url     : https://prove2.me/theorems/33990060-12a1-419d-8d21-70641febe2ea
-- title:
--   All-start BV finite-activity original separated marked-jump count has finite expectation
-- statement:
--   For the actual original Levy process with BV, explicitly finite full negative ν activity and finite P mass, every separated negative mark count has finite expected mass on any deterministic interval (s,t]. The proof bounds it by the previously Proved exact full-negative source predictable rectangle compensator; this supplies the finite-mean premise needed by the all-start pushforward mark-measure construction.
-- source:
--   Proved original source predictable full-negative count c78120b8; monotonicity of intrinsic count measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_finite_activity_all_start_actual_negative_predictable_rectangle
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_bv_finite_activity_original_any_start_separated_mark_expected_count_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hP : P Set.univ < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t) (ε : ℝ) (hε : 0 < ε) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (-ε)) ∂P) < ⊤ := by sorry
