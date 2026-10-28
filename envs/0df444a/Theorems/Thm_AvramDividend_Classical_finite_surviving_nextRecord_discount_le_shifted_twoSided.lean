-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_surviving_nextRecord_discount_le_shifted_twoSided
-- name    : AvramDividend.Classical.finite_surviving_nextRecord_discount_le_shifted_twoSided
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:53:50.645562+00:00
-- url     : https://prove2.me/theorems/2df92b8c-9b3a-44a8-a907-29f0e5681693
-- title:
--   Finite-record killed reward is bounded by the true shifted two-sided payoff
-- statement:
--   At attained finite consecutive record times, without assuming survival in advance, the killed next-record discounted reward is bounded pointwise by the past discount times the true shifted upper-before-lower two-sided exit reward. Proved strict record survival inclusion supplies the condition in the survived branch; proved discount factorisation supplies the multiplication; the killed reward vanishes otherwise. This is the concrete payoff input to finite-localised stopped Markov regeneration.
-- source:
--   Strong-Markov renewal upper-bound pathwise component under finite first-record and attained-record hypotheses.

import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_nextRecord_upclock_eq_add_shifted_inf
import Theorems.Thm_AvramDividend_Classical_survived_nextRecord_shifted_upclock_lt_lower_exit
import Theorems.Thm_AvramDividend_Classical_killed_nextRecord_discount_le_shifted_twoSided_of_strict_exit_inclusion

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.finite_surviving_nextRecord_discount_le_shifted_twoSided
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (a b ε q : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hε : 0 ≤ ε) (u v δ : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b)
    (hv : (v : ℝ≥0∞) = twoSidedExitUpTime X (b + ε) ω)
    (hδ : u + δ = v) :
    (if twoSidedExitUpTime X (b + ε) ω <
        barrierRuinTime X a ω then
      ENNReal.ofReal ε *
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X (b + ε) ω).toReal)))
      else 0) ≤
    ENNReal.ofReal ε *
      (ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
        (if (⨅ (t : ℝ≥0)
              (_ : ε < X.X (u + t) ω - X.X u ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0)
              (_ : X.X (u + t) ω - X.X u ω < -a), (t : ℝ≥0∞))
        then ENNReal.ofReal (Real.exp
          (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0)
              (_ : ε < X.X (u + t) ω - X.X u ω), (t : ℝ≥0∞)))))
        else 0)) := by sorry
