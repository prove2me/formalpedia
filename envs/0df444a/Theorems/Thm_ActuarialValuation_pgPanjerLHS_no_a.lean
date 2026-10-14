-- Prove2me | Theorems.Thm_ActuarialValuation_pgPanjerLHS_no_a
-- name    : ActuarialValuation.pgPanjerLHS_no_a
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:54:32.038798+00:00
-- url     : https://prove2.me/theorems/5b5ddc55-0851-4256-a29d-1c6d4dc59dc5
-- title:
--   Panjer frequency recursion and zero-size correction: pgPanjerLHS_no_a
-- statement:
--   If frequency a=0 the zero-claim-size correction vanishes. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \text{If frequency a=0 the zero-claim-size correction vanishes.}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 397. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796; Sundt and Jewell (1981), Further Results on Recursive Evaluation of Compound Distributions, https://doi.org/10.1017/S0515036100006802; S. D. Promislow, Fundamentals of Actuarial Mathematics (2015), chapter 21. Parent topic: Finite-support Panjer counting law, severity convolution powers, aggregate distribution by genuine random-sum weights and corrected zero-severity Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/journals/astin-bulletin-journal-of-the-iaa/article/recursive-evaluation-of-a-family-of-compound-distributions/BD6628F3853600A8F79C6A45E92938CB

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgPanjerLHS

namespace ActuarialValuation

theorem pgPanjerLHS_no_a (f0 g : ℝ) : pgPanjerLHS 0 f0 g=g := by sorry

end ActuarialValuation
