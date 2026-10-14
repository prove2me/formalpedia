-- Prove2me | Theorems.Thm_ActuarialValuation_pgAggregateCDF_monotone
-- name    : ActuarialValuation.pgAggregateCDF_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:56:29.829761+00:00
-- url     : https://prove2.me/theorems/9409656c-ffc9-455b-8065-687f62e833fe
-- title:
--   Aggregate moments, solvency and recursive valuation: pgAggregateCDF_monotone
-- statement:
--   A true compound aggregate CDF is nondecreasing for valid probability masses. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{A true compound aggregate CDF is nondecreasing for valid} \\ \text{probability masses.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 397. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796; Sundt and Jewell (1981), Further Results on Recursive Evaluation of Compound Distributions, https://doi.org/10.1017/S0515036100006802; S. D. Promislow, Fundamentals of Actuarial Mathematics (2015), chapter 21. Parent topic: Finite-support Panjer counting law, severity convolution powers, aggregate distribution by genuine random-sum weights and corrected zero-severity Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/journals/astin-bulletin-journal-of-the-iaa/article/recursive-evaluation-of-a-family-of-compound-distributions/BD6628F3853600A8F79C6A45E92938CB

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgAggregateCDF

namespace ActuarialValuation

theorem pgAggregateCDF_monotone (p f : ℕ → ℝ) (m k : ℕ) (hp : ∀ j, 0 ≤ p j) (hf : ∀ j, 0 ≤ f j) : pgAggregateCDF p f m k ≤ pgAggregateCDF p f m (k+1) := by sorry

end ActuarialValuation
