-- Prove2me | Theorems.Thm_ActuarialValuation_gamblerFairSuccess_target
-- name    : ActuarialValuation.gamblerFairSuccess_target
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:30:36.652779+00:00
-- url     : https://prove2.me/theorems/55eab61f-2223-476e-818a-dd2596e94336
-- title:
--   Fair harmonic function equals one at positive upper target
-- statement:
--   At positive target capital N, the fair success candidate equals N divided by itself, giving the upper absorbing boundary condition one. The positive target hypothesis excludes dividing zero by zero.
--
--   **Mathematical statement**
--
--   $$
--   N>0\Rightarrow H_{\rm fair}(N)=1
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 427 (Library PDF page 453), parent framework: Examples 23.4–23.5 (gambler's ruin). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration ActuarialValuation.gamblerFairSuccess_target is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gamblerFairSuccess

namespace ActuarialValuation

theorem gamblerFairSuccess_target (N : ℕ) (hN : 0 < N) :
  gamblerFairSuccess N N = 1 := by sorry

end ActuarialValuation
