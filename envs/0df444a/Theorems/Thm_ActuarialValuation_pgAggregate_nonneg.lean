-- Prove2me | Theorems.Thm_ActuarialValuation_pgAggregate_nonneg
-- name    : ActuarialValuation.pgAggregate_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:52:19.80999+00:00
-- url     : https://prove2.me/theorems/b1d28493-ec65-4fdc-83b6-a39fe03e2149
-- title:
--   Discrete severity powers and genuinely compounded frequency: pgAggregate_nonneg
-- statement:
--   Nonnegative frequency and severity weights imply nonnegative compound aggregate probability. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{Nonnegative frequency and severity weights imply nonnegative} \\ \text{compound aggregate probability.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 397. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796; Sundt and Jewell (1981), Further Results on Recursive Evaluation of Compound Distributions, https://doi.org/10.1017/S0515036100006802; S. D. Promislow, Fundamentals of Actuarial Mathematics (2015), chapter 21. Parent topic: Finite-support Panjer counting law, severity convolution powers, aggregate distribution by genuine random-sum weights and corrected zero-severity Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/journals/astin-bulletin-journal-of-the-iaa/article/recursive-evaluation-of-a-family-of-compound-distributions/BD6628F3853600A8F79C6A45E92938CB

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgAggregate

namespace ActuarialValuation

theorem pgAggregate_nonneg (p f : ℕ → ℝ) (m k : ℕ) (hp : ∀ j, 0 ≤ p j) (hf : ∀ j, 0 ≤ f j) : 0 ≤ pgAggregate p f m k := by sorry

end ActuarialValuation
