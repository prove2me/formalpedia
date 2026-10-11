-- Prove2me | Theorems.Thm_ActuarialValuation_pgPanjerFinite_fundamental
-- name    : ActuarialValuation.pgPanjerFinite_fundamental
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T15:58:42.746313+00:00
-- url     : https://prove2.me/theorems/3d71a1ec-ce68-4250-a8bd-b58847098ed1
-- title:
--   Aggregate moments, solvency and recursive valuation: pgPanjerFinite_fundamental
-- statement:
--   The full corrected positive Panjer recurrence follows from the independently defined finite frequency/severity random-sum distribution, for all k>0, including zero-sized individual claims and a genuine frequency upper bound. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{The full corrected positive Panjer recurrence follows from the} \\ \text{independently defined finite frequency/severity random-sum} \\ \text{distribution, for all k>0, including zero-sized individual} \\ \text{claims and a genuine frequency upper bound.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 397. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796; Sundt and Jewell (1981), Further Results on Recursive Evaluation of Compound Distributions, https://doi.org/10.1017/S0515036100006802; S. D. Promislow, Fundamentals of Actuarial Mathematics (2015), chapter 21. Parent topic: Finite-support Panjer counting law, severity convolution powers, aggregate distribution by genuine random-sum weights and corrected zero-severity Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/journals/astin-bulletin-journal-of-the-iaa/article/recursive-evaluation-of-a-family-of-compound-distributions/BD6628F3853600A8F79C6A45E92938CB

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgAggregate
import Definitions.Def_actuarial_pgCountPGF
import Definitions.Def_actuarial_pgPanjerLHS
import Definitions.Def_actuarial_pgPanjerRHS
import Definitions.Def_actuarial_pgPanjerRecLaw
import Definitions.Def_actuarial_pgCountSupport

namespace ActuarialValuation

theorem pgPanjerFinite_fundamental (a b : ℝ) (p f : ℕ → ℝ) (m : ℕ) (hr : pgPanjerRecLaw a b p m) (hs : pgCountSupport p m) : (pgAggregate p f m 0 = pgCountPGF p m (f 0)) ∧ (∀ k : ℕ, 0<k → pgPanjerLHS a (f 0) (pgAggregate p f m k) = pgPanjerRHS a b f (pgAggregate p f m) k) := by sorry

end ActuarialValuation
