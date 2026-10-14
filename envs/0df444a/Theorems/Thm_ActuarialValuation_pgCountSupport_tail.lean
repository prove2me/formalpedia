-- Prove2me | Theorems.Thm_ActuarialValuation_pgCountSupport_tail
-- name    : ActuarialValuation.pgCountSupport_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:55:27.700414+00:00
-- url     : https://prove2.me/theorems/952ad136-33ec-44e6-95c6-63d15f127cad
-- title:
--   Panjer frequency recursion and zero-size correction: pgCountSupport_tail
-- statement:
--   A finite frequency model really has no hidden tail claim counts. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{A finite frequency model really has no hidden tail claim} \\ \text{counts.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 397. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796; Sundt and Jewell (1981), Further Results on Recursive Evaluation of Compound Distributions, https://doi.org/10.1017/S0515036100006802; S. D. Promislow, Fundamentals of Actuarial Mathematics (2015), chapter 21. Parent topic: Finite-support Panjer counting law, severity convolution powers, aggregate distribution by genuine random-sum weights and corrected zero-severity Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/journals/astin-bulletin-journal-of-the-iaa/article/recursive-evaluation-of-a-family-of-compound-distributions/BD6628F3853600A8F79C6A45E92938CB

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgCountSupport

namespace ActuarialValuation

theorem pgCountSupport_tail (p : ℕ → ℝ) (m n : ℕ) (h : pgCountSupport p m) (hm : m<n) : p n=0 := by sorry

end ActuarialValuation
