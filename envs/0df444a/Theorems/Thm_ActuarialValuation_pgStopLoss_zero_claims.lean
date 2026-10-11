-- Prove2me | Theorems.Thm_ActuarialValuation_pgStopLoss_zero_claims
-- name    : ActuarialValuation.pgStopLoss_zero_claims
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T15:58:03.632544+00:00
-- url     : https://prove2.me/theorems/1f21e8ce-a515-48ba-9b04-8d694fb8b5e5
-- title:
--   Aggregate moments, solvency and recursive valuation: pgStopLoss_zero_claims
-- statement:
--   At zero retention, expected excess-of-loss equals the truncated expected total loss. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{At zero retention, expected excess-of-loss equals the truncated} \\ \text{expected total loss.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 397. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796; Sundt and Jewell (1981), Further Results on Recursive Evaluation of Compound Distributions, https://doi.org/10.1017/S0515036100006802; S. D. Promislow, Fundamentals of Actuarial Mathematics (2015), chapter 21. Parent topic: Finite-support Panjer counting law, severity convolution powers, aggregate distribution by genuine random-sum weights and corrected zero-severity Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/journals/astin-bulletin-journal-of-the-iaa/article/recursive-evaluation-of-a-family-of-compound-distributions/BD6628F3853600A8F79C6A45E92938CB

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgAggregate
import Definitions.Def_actuarial_pgStopLoss

namespace ActuarialValuation

theorem pgStopLoss_zero_claims (p f : ℕ → ℝ) (m k : ℕ) : pgStopLoss p f m k 0 = ∑ j ∈ Finset.range (k+1), pgAggregate p f m j * (j:ℝ) := by sorry

end ActuarialValuation
