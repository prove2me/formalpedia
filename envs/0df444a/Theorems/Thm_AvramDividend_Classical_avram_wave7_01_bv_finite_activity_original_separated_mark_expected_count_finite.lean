-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_finite_activity_original_separated_mark_expected_count_finite
-- name    : AvramDividend.Classical.avram_wave7_01_bv_finite_activity_original_separated_mark_expected_count_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:28:03.108935+00:00
-- url     : https://prove2.me/theorems/08133394-84ff-4c0e-847c-0ef2d8b7aa35
-- title:
--   Finite-activity BV original negative cutoff mark count has finite expectation
-- statement:
--   On the unchanged original Lévy sample space, if X is BV, ν((-∞,0)) is explicitly finite and the original ambient P has finite mass, then actual negative jumps separated from zero have finite expected intrinsic count on the finite interval (0,T]. The proof bounds the separated jump count by the Proved exact full-negative original-process BV finite-activity compensator. No inference of finite activity from BV is made.
-- source:
--   Proved all-start exact full-negative original predictable rectangle c78120b8, count measure monotonicity

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_finite_activity_all_start_actual_negative_predictable_rectangle
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_bv_finite_activity_original_separated_mark_expected_count_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hP : P Set.univ < ⊤)
    (T : ℝ≥0) (ε : ℝ) (hε : 0 < ε) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-ε)) ∂P) < ⊤ := by sorry
