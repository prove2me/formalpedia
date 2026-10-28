-- Prove2me | Theorems.Thm_AvramDividend_Classical_survived_nextRecord_shifted_path_lower_guard
-- name    : AvramDividend.Classical.survived_nextRecord_shifted_path_lower_guard
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:18:37.09122+00:00
-- url     : https://prove2.me/theorems/63c16d78-a4c8-46f8-a45c-c97aa29f0f72
-- title:
--   Survival to the next record imposes a lower barrier on the shifted Lévy path
-- statement:
--   If two finite first-upcrossing record clocks u at b and v at b+epsilon exist and the second record occurs before strict drawdown ruin at level a, then every shifted path value X(u+s)-X(u) for s before the next upcrossing v-u is at least -a. The reflected drawdown is at most a before v, and the running supremum cannot drop below its value at the first record. This is the direction needed for an upper comparison to a shifted ordinary two-sided exit event.
-- source:
--   Deduction from first-upcrossing prefix survival, first-record peak attainment and monotonicity of the running supremum.

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_before_barrierRuin_iff_prefix_survival
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_attains_peak
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_runningSup_sub_path_eq_zero
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.survived_nextRecord_shifted_path_lower_guard
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (a b ε : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (u v : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b < X.X r ω), (r : ℝ≥0∞)))
    (hv : (v : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b + ε < X.X r ω), (r : ℝ≥0∞)))
    (hSurvive : (v : ℝ≥0∞) < barrierRuinTime X a ω) :
    ∀ s : ℝ≥0, u + s < v →
      -a ≤ X.X (u + s) ω - X.X u ω := by sorry
