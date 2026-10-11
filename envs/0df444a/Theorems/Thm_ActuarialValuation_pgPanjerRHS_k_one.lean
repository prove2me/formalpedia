-- Prove2me | Theorems.Thm_ActuarialValuation_pgPanjerRHS_k_one
-- name    : ActuarialValuation.pgPanjerRHS_k_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:54:57.092528+00:00
-- url     : https://prove2.me/theorems/06a6b2bf-0310-42a7-95d5-ebe8519e9314
-- title:
--   Panjer frequency recursion and zero-size correction: pgPanjerRHS_k_one
-- statement:
--   The first strictly positive aggregate atom is the corrected Bernoulli-style recurrence. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{The first strictly positive aggregate atom is the corrected} \\ \text{Bernoulli-style recurrence.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 397. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796; Sundt and Jewell (1981), Further Results on Recursive Evaluation of Compound Distributions, https://doi.org/10.1017/S0515036100006802; S. D. Promislow, Fundamentals of Actuarial Mathematics (2015), chapter 21. Parent topic: Finite-support Panjer counting law, severity convolution powers, aggregate distribution by genuine random-sum weights and corrected zero-severity Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/journals/astin-bulletin-journal-of-the-iaa/article/recursive-evaluation-of-a-family-of-compound-distributions/BD6628F3853600A8F79C6A45E92938CB

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgPanjerRHS

namespace ActuarialValuation

theorem pgPanjerRHS_k_one (a b : ℝ) (f g : ℕ → ℝ) : pgPanjerRHS a b f g 1=(a+b)*f 1*g 0 := by sorry

end ActuarialValuation
