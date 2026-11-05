-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_finite_compact_test_mark_lintegral
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_finite_compact_test_mark_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:34:02.990407+00:00
-- url     : https://prove2.me/theorems/920d7927-bcbe-4730-ae1a-63182fc1fc00
-- title:
--   Actual original finite compact negative jump test equals time-mark count-measure lintegral pathwise
-- statement:
--   For each genuine original spectrally negative Lévy path and a continuous real test that vanishes near zero, the finite set of relevant jump times represents the exact integral of the nonnegative transformed test against the actual original marked jump count measure restricted to the finite time interval. This is the pathwise count integral to genuine finite jump sum bridge required to identify the expected intrinsic mark measure by compact tests; no compensator is assumed.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_test_jump_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_intrinsic_nonnegative_test_lintegral

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_finite_compact_test_mark_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0)
    (g : ℝ → ℝ) (hg : Continuous g)
    (ε : ℝ) (hε : 0 < ε)
    (hvanish : ∀ y : ℝ, dist y 0 < ε → g y = 0) :
    ∃ F : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧
        g (X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0) ∧
      (∫⁻ p : ℝ≥0 × ℝ,
        (if p.1 ∈ Ioc (0 : ℝ≥0) T then
          ENNReal.ofReal (g p.2) else 0) ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 =>
            (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
        ∑ u ∈ F, ENNReal.ofReal (g (X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) := by sorry
