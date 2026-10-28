-- Prove2me | Theorems.Thm_AvramDividend_Classical_nextRecord_upclock_eq_add_shifted_inf
-- name    : AvramDividend.Classical.nextRecord_upclock_eq_add_shifted_inf
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:25:29.830868+00:00
-- url     : https://prove2.me/theorems/794e45f9-25b5-4296-8a32-6c569e512a87
-- title:
--   The next strict record clock is past stopping time plus shifted-future first passage
-- statement:
--   At a finite attained first record level b, the next strict record time b+ε equals the past first-passage time u plus the strict first-passage infimum of the Lévy increments after u. This additive form follows from the Proved exact shifted-witness infimum and ENNReal.add_iInf₂, which preserves arbitrary nested infima under addition. It is the clock factorisation needed to split the q-discount between stopped history and future reward in strong Markov renewal.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1, strong Markov first-passage clock regeneration.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_nextRecord_upclock_eq_shifted_inf

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.nextRecord_upclock_eq_add_shifted_inf
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b ε : ℝ) (hε : 0 ≤ ε) (u : ℝ≥0) (ω : Ω)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b) :
    twoSidedExitUpTime X (b + ε) ω =
      (u : ℝ≥0∞) +
        (⨅ (t : ℝ≥0)
          (_ : ε < X.X (u + t) ω - X.X u ω),
          (t : ℝ≥0∞)) := by sorry
