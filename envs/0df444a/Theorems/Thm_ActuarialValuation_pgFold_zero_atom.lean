-- Prove2me | Theorems.Thm_ActuarialValuation_pgFold_zero_atom
-- name    : ActuarialValuation.pgFold_zero_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:50:51.007367+00:00
-- url     : https://prove2.me/theorems/d2fb36bb-9de7-4674-9b7c-bf322e6b2ae4
-- title:
--   Discrete severity powers and genuinely compounded frequency: pgFold_zero_atom
-- statement:
--   Probability of aggregate zero with n independent claims is f_0 to the nth power. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{Probability of aggregate zero with n independent claims is f\_0} \\ \text{to the nth power.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 397. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796; Sundt and Jewell (1981), Further Results on Recursive Evaluation of Compound Distributions, https://doi.org/10.1017/S0515036100006802; S. D. Promislow, Fundamentals of Actuarial Mathematics (2015), chapter 21. Parent topic: Finite-support Panjer counting law, severity convolution powers, aggregate distribution by genuine random-sum weights and corrected zero-severity Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/journals/astin-bulletin-journal-of-the-iaa/article/recursive-evaluation-of-a-family-of-compound-distributions/BD6628F3853600A8F79C6A45E92938CB

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgFold

namespace ActuarialValuation

theorem pgFold_zero_atom (f : ℕ → ℝ) (n : ℕ) : pgFold f n 0 = (f 0)^n := by sorry

end ActuarialValuation
