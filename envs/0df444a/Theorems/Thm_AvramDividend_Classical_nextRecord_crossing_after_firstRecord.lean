-- Prove2me | Theorems.Thm_AvramDividend_Classical_nextRecord_crossing_after_firstRecord
-- name    : AvramDividend.Classical.nextRecord_crossing_after_firstRecord
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:01:05.996545+00:00
-- url     : https://prove2.me/theorems/b7a7e178-4ea8-4807-ba89-1f1691b1cf25
-- title:
--   A higher record crossing occurs after the first record and crosses the shifted increment
-- statement:
--   If u is the genuine first strict upward crossing time of b and X_u=b, every observation t at which X_t>b+ε with ε≥0 must occur at or after u; its increment above X_u then exceeds ε. This reverse witness inclusion complements the Proved nextRecord_upclock_le_shifted_witness and is a pathwise prerequisite for translating consecutive strict record clocks under the strong Markov property.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1, strict first-record renewal pathwise clock translation.

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.nextRecord_crossing_after_firstRecord
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b ε : ℝ) (hε : 0 ≤ ε) (u t : ℝ≥0) (ω : Ω)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b)
    (hNext : b + ε < X.X t ω) :
    u ≤ t ∧ ε < X.X t ω - X.X u ω := by sorry
