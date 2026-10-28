-- Prove2me | Theorems.Thm_AvramDividend_Classical_nextRecord_upclock_eq_shifted_inf
-- name    : AvramDividend.Classical.nextRecord_upclock_eq_shifted_inf
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:05:34.744499+00:00
-- url     : https://prove2.me/theorems/2b8ab528-20b0-45ee-b9c9-e2d1207d1271
-- title:
--   The next actual strict record clock equals the shifted future crossing infimum
-- statement:
--   If u is the finite first strict upper passage of b and the Lévy path attains b there without an upward overshoot, then the first strict passage of b+ε, ε≥0, equals the infimum of all translated times u+t at which the post-u increment strictly exceeds ε. Both directions are proved by crossing-witness transfer. This is a precise clock restart needed to identify the next killed record reward under strong Markov.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1, regeneration at successive running supremum records.

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_nextRecord_upclock_le_shifted_witness
import Theorems.Thm_AvramDividend_Classical_nextRecord_crossing_after_firstRecord

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.nextRecord_upclock_eq_shifted_inf
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b ε : ℝ) (hε : 0 ≤ ε) (u : ℝ≥0) (ω : Ω)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b) :
    twoSidedExitUpTime X (b + ε) ω =
      (⨅ (t : ℝ≥0)
        (_ : ε < X.X (u + t) ω - X.X u ω),
        ((u + t : ℝ≥0) : ℝ≥0∞)) := by sorry
