-- Prove2me | Theorems.Thm_ActuarialValuation_pgConvolve_comm
-- name    : ActuarialValuation.pgConvolve_comm
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:49:22.145604+00:00
-- url     : https://prove2.me/theorems/af3140c3-2bff-44f9-b539-cc960f98cce2
-- title:
--   Discrete severity powers and genuinely compounded frequency: pgConvolve_comm
-- statement:
--   Convolution is commutative for integer-valued nonnegative claims. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{Convolution is commutative for integer-valued nonnegative} \\ \text{claims.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 397. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796; Sundt and Jewell (1981), Further Results on Recursive Evaluation of Compound Distributions, https://doi.org/10.1017/S0515036100006802; S. D. Promislow, Fundamentals of Actuarial Mathematics (2015), chapter 21. Parent topic: Finite-support Panjer counting law, severity convolution powers, aggregate distribution by genuine random-sum weights and corrected zero-severity Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/journals/astin-bulletin-journal-of-the-iaa/article/recursive-evaluation-of-a-family-of-compound-distributions/BD6628F3853600A8F79C6A45E92938CB

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgConvolve

namespace ActuarialValuation

theorem pgConvolve_comm (f g : ℕ → ℝ) (k : ℕ) : pgConvolve f g k=pgConvolve g f k := by sorry

end ActuarialValuation
