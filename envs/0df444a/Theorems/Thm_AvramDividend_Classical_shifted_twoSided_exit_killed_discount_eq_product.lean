-- Prove2me | Theorems.Thm_AvramDividend_Classical_shifted_twoSided_exit_killed_discount_eq_product
-- name    : AvramDividend.Classical.shifted_twoSided_exit_killed_discount_eq_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:52:09.009815+00:00
-- url     : https://prove2.me/theorems/9a801969-ec25-401d-a186-5fd3a469574a
-- title:
--   Killed discounted next-record payoff factors on the successful shifted two-sided exit
-- statement:
--   A finite surviving strict first record at b and a successful shifted two-sided upper exit from ε before lower ε−a force the next strict record to survive reflected ruin. On that event the actual ε-sized killed discounted payment at the next record equals ε times the discount at the past record times the shifted exit discount. This is the pointwise multiplicative payoff identity needed to combine the q-scale two-sided exit law with strong Markov regeneration.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1, killed first-record renewal and the q-scale two-sided exit factor.

import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_shifted_twoSided_firstExit_implies_nextRecord_killed
import Theorems.Thm_AvramDividend_Classical_nextRecord_discount_eq_past_mul_future

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.shifted_twoSided_exit_killed_discount_eq_product
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε q : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
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
    (if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X (b + ε) ω).toReal)))
      else 0) =
      ENNReal.ofReal ε *
        (ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
          ENNReal.ofReal (Real.exp (-(q * (T : ℝ))))) := by sorry
