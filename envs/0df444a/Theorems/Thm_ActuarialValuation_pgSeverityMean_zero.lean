-- Prove2me | Theorems.Thm_ActuarialValuation_pgSeverityMean_zero
-- name    : ActuarialValuation.pgSeverityMean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:58:29.11253+00:00
-- url     : https://prove2.me/theorems/e8450d8c-4fee-4e98-9d0b-9ecf23a1afd5
-- title:
--   Aggregate moments, solvency and recursive valuation: pgSeverityMean_zero
-- statement:
--   A severity supported only at zero has zero expected claim size. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \text{A severity supported only at zero has zero expected claim size.}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 397. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796; Sundt and Jewell (1981), Further Results on Recursive Evaluation of Compound Distributions, https://doi.org/10.1017/S0515036100006802; S. D. Promislow, Fundamentals of Actuarial Mathematics (2015), chapter 21. Parent topic: Finite-support Panjer counting law, severity convolution powers, aggregate distribution by genuine random-sum weights and corrected zero-severity Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/journals/astin-bulletin-journal-of-the-iaa/article/recursive-evaluation-of-a-family-of-compound-distributions/BD6628F3853600A8F79C6A45E92938CB

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgSeverityMean

namespace ActuarialValuation

theorem pgSeverityMean_zero (f : ℕ → ℝ) : pgSeverityMean f 0=0 := by sorry

end ActuarialValuation
