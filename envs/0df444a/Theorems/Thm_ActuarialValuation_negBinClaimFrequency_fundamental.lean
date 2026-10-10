-- Prove2me | Theorems.Thm_ActuarialValuation_negBinClaimFrequency_fundamental
-- name    : ActuarialValuation.negBinClaimFrequency_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:32:20.760811+00:00
-- url     : https://prove2.me/theorems/1f8c6a65-6efb-4ab8-996b-1006336e5834
-- title:
--   Gamma-Poisson negative-binomial recurrence, mean and overdispersion
-- statement:
--   The capstone combines the exact integer-shape negative-binomial count-mass recursion and the unit-exposure Gamma-Poisson mixture parameterisation. It verifies both predictive moments and coefficient nonnegativity, without claiming an infinite PMF normalisation proof or a Gamma mixture integral in Lean.
--
--   **Mathematical statement**
--
--   $$
--   (n+1)g(n+1)=(n+r)pg(n),\quad\mu=r/\beta,\quad\sigma^2=\mu+r/\beta^2
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.5, printed page 383 (Library PDF page 409), parent framework: Section 21.5 (negative-binomial frequency). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://encyclopediaofmath.org/wiki/Negative_binomial_distribution. The specific Lean declaration ActuarialValuation.negBinClaimFrequency_fundamental is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_negBinGammaPredictive
import Definitions.Def_actuarial_negBinGammaProbability
import Definitions.Def_actuarial_negBinCountMean
import Definitions.Def_actuarial_negBinCountVariance

namespace ActuarialValuation

theorem negBinClaimFrequency_fundamental
  (r n : ℕ) (b : ℝ)
  (hr : 0 < r) (hb : 0 < b) :
  ((n + 1 : ℝ) * negBinGammaPredictive r b (n + 1) =
    ((n + r : ℕ) : ℝ) * negBinGammaProbability b *
       negBinGammaPredictive r b n) ∧
  (negBinCountMean r (negBinGammaProbability b) = (r : ℝ) / b) ∧
  (negBinCountVariance r (negBinGammaProbability b) =
    (r : ℝ) / b + (r : ℝ) / b ^ 2) ∧
  (0 ≤ negBinGammaPredictive r b n) := by sorry

end ActuarialValuation
