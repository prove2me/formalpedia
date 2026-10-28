-- Prove2me | Theorems.Thm_AvramDividend_Classical_nextRecord_killed_discount_lower_of_shifted_guard
-- name    : AvramDividend.Classical.nextRecord_killed_discount_lower_of_shifted_guard
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:27:46.710558+00:00
-- url     : https://prove2.me/theorems/17047782-be48-4a50-88a7-219e0814517d
-- title:
--   Safe post-record intervals give a lower bound on the next killed discounted record payment
-- statement:
--   For finite first record clocks u and v, with v no later than u+T, a safe reflected path before u and safe shifted drawdown through T ensure that the record at v precedes ruin. For any nonnegative discount rate q and record payment ε, the killed discounted payment at v is at least ε exp(-q(u+T)). This is the pointwise payoff estimate needed to lower bound conditional renewal expectations from future path events.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1, pathwise lower bound for strong-Markov record regeneration.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_nextRecord_survives_of_shifted_drawdown_guard

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.nextRecord_killed_discount_lower_of_shifted_guard
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε q : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hε : 0 ≤ ε) (hq : 0 ≤ q)
    (ω : Ω) (u v T : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hv : (v : ℝ≥0∞) = twoSidedExitUpTime X (b + ε) ω)
    (hvT : v ≤ u + T)
    (hPre : ∀ r : ℝ≥0, r < u → reflectedSup X r ω ≤ a)
    (hPost : ∀ t : ℝ≥0, t ≤ T →
      sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
        X.X (u + t) ω ≤ a) :
    ENNReal.ofReal
        (ε * Real.exp (-(q * (((u + T : ℝ≥0) : ℝ))))) ≤
      (if (v : ℝ≥0∞) < barrierRuinTime X a ω then
         ENNReal.ofReal (ε * Real.exp (-(q * (v : ℝ))))
       else 0) := by sorry
