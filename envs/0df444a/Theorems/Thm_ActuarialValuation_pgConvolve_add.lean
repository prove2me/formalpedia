-- Prove2me | Theorems.Thm_ActuarialValuation_pgConvolve_add
-- name    : ActuarialValuation.pgConvolve_add
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T15:49:44.811208+00:00
-- url     : https://prove2.me/theorems/32463609-d10b-4cff-9014-1adb11af38f0
-- title:
--   Discrete severity powers and genuinely compounded frequency: pgConvolve_add
-- statement:
--   Convolution respects linear mixtures of independent claim-size laws. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{Convolution respects linear mixtures of independent claim-size} \\ \text{laws.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 397. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796; Sundt and Jewell (1981), Further Results on Recursive Evaluation of Compound Distributions, https://doi.org/10.1017/S0515036100006802; S. D. Promislow, Fundamentals of Actuarial Mathematics (2015), chapter 21. Parent topic: Finite-support Panjer counting law, severity convolution powers, aggregate distribution by genuine random-sum weights and corrected zero-severity Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/journals/astin-bulletin-journal-of-the-iaa/article/recursive-evaluation-of-a-family-of-compound-distributions/BD6628F3853600A8F79C6A45E92938CB

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgConvolve

namespace ActuarialValuation

theorem pgConvolve_add (f g h : ℕ → ℝ) (k : ℕ) : pgConvolve f (fun j => g j+h j) k = pgConvolve f g k+pgConvolve f h k := by sorry

end ActuarialValuation
