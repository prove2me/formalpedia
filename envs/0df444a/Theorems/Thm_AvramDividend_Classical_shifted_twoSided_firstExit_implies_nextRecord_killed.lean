-- Prove2me | Theorems.Thm_AvramDividend_Classical_shifted_twoSided_firstExit_implies_nextRecord_killed
-- name    : AvramDividend.Classical.shifted_twoSided_firstExit_implies_nextRecord_killed
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:45:34.22807+00:00
-- url     : https://prove2.me/theorems/45333e12-dce2-4872-80f1-fae029bb760f
-- title:
--   A successful shifted two-sided up-exit produces a surviving next record of the reflected Lévy process
-- statement:
--   At an attained finite first record u below the reflected ruin horizon, let T be the finite first future strict upcrossing of increment ε. If that upper exit occurs strictly before the shifted future path falls below ε−a, then the true next record at b+ε occurs before the original reflected ruin time. The proof identifies the global next clock u+T, uses no-positive-jump creeping to attain the upper boundary, keeps the full shifted path within the width-a strip through T, and invokes the proved strip-to-drawdown and killed-record survival lemmas. This is the exact pathwise event inclusion required to apply the two-sided q-scale exit law to the strong-Markov renewal lower bound.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1, lower record-renewal step via two-sided q-scale exit before reflected ruin.

import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_raw_twoSidedFutureExit_prefix_strip
import Theorems.Thm_AvramDividend_Classical_shifted_future_strip_implies_drawdown_guard
import Theorems.Thm_AvramDividend_Classical_nextRecord_upclock_eq_add_shifted_inf
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold
import Theorems.Thm_AvramDividend_Classical_nextRecord_killed_survival_of_shifted_guard

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.shifted_twoSided_firstExit_implies_nextRecord_killed
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (ω : Ω) (u T : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b)
    (hBefore : (u : ℝ≥0∞) < barrierRuinTime X a ω)
    (hUp : (T : ℝ≥0∞) =
      (⨅ (r : ℝ≥0)
        (_ : ε < X.X (u + r) ω - X.X u ω), (r : ℝ≥0∞)))
    (hUpBeforeDown : (T : ℝ≥0∞) <
      (⨅ (r : ℝ≥0)
        (_ : X.X (u + r) ω - X.X u ω < ε - a),
        (r : ℝ≥0∞))) :
    twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω := by sorry
