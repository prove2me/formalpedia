-- Prove2me | Theorems.Thm_ActuarialValuation_pgAggregateCDF_succ
-- name    : ActuarialValuation.pgAggregateCDF_succ
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:56:09.34624+00:00
-- url     : https://prove2.me/theorems/218a46ce-407c-4550-a7a1-f2459ee0153b
-- title:
--   Aggregate moments, solvency and recursive valuation: pgAggregateCDF_succ
-- statement:
--   The cumulative aggregate claim law accumulates exactly one additional severity atom. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{The cumulative aggregate claim law accumulates exactly one} \\ \text{additional severity atom.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 397. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796; Sundt and Jewell (1981), Further Results on Recursive Evaluation of Compound Distributions, https://doi.org/10.1017/S0515036100006802; S. D. Promislow, Fundamentals of Actuarial Mathematics (2015), chapter 21. Parent topic: Finite-support Panjer counting law, severity convolution powers, aggregate distribution by genuine random-sum weights and corrected zero-severity Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/journals/astin-bulletin-journal-of-the-iaa/article/recursive-evaluation-of-a-family-of-compound-distributions/BD6628F3853600A8F79C6A45E92938CB

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgAggregate
import Definitions.Def_actuarial_pgAggregateCDF

namespace ActuarialValuation

theorem pgAggregateCDF_succ (p f : ℕ → ℝ) (m k : ℕ) : pgAggregateCDF p f m (k+1)=pgAggregateCDF p f m k+pgAggregate p f m (k+1) := by sorry

end ActuarialValuation
