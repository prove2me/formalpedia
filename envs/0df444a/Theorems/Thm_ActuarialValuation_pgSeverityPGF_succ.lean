-- Prove2me | Theorems.Thm_ActuarialValuation_pgSeverityPGF_succ
-- name    : ActuarialValuation.pgSeverityPGF_succ
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:53:13.629819+00:00
-- url     : https://prove2.me/theorems/3d2c8f9b-1929-48fe-b08a-aedbea28351f
-- title:
--   Discrete severity powers and genuinely compounded frequency: pgSeverityPGF_succ
-- statement:
--   Adding the next severity atom increases its generating polynomial by the correct term. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{Adding the next severity atom increases its generating} \\ \text{polynomial by the correct term.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 397. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796; Sundt and Jewell (1981), Further Results on Recursive Evaluation of Compound Distributions, https://doi.org/10.1017/S0515036100006802; S. D. Promislow, Fundamentals of Actuarial Mathematics (2015), chapter 21. Parent topic: Finite-support Panjer counting law, severity convolution powers, aggregate distribution by genuine random-sum weights and corrected zero-severity Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/journals/astin-bulletin-journal-of-the-iaa/article/recursive-evaluation-of-a-family-of-compound-distributions/BD6628F3853600A8F79C6A45E92938CB

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgSeverityPGF

namespace ActuarialValuation

theorem pgSeverityPGF_succ (f : ℕ → ℝ) (m : ℕ) (z : ℝ) : pgSeverityPGF f (m+1) z=pgSeverityPGF f m z+f (m+1)*z^(m+1) := by sorry

end ActuarialValuation
