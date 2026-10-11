-- Prove2me | Theorems.Thm_ActuarialValuation_pgConvolve_zero
-- name    : ActuarialValuation.pgConvolve_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:48:19.240576+00:00
-- url     : https://prove2.me/theorems/bee5e05d-0887-4a19-9e2b-4a25a1bbd34b
-- title:
--   Discrete severity powers and genuinely compounded frequency: pgConvolve_zero
-- statement:
--   The zero atom requires both independent severities to be zero. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \text{The zero atom requires both independent severities to be zero.}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 397. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796; Sundt and Jewell (1981), Further Results on Recursive Evaluation of Compound Distributions, https://doi.org/10.1017/S0515036100006802; S. D. Promislow, Fundamentals of Actuarial Mathematics (2015), chapter 21. Parent topic: Finite-support Panjer counting law, severity convolution powers, aggregate distribution by genuine random-sum weights and corrected zero-severity Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/journals/astin-bulletin-journal-of-the-iaa/article/recursive-evaluation-of-a-family-of-compound-distributions/BD6628F3853600A8F79C6A45E92938CB

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgConvolve

namespace ActuarialValuation

theorem pgConvolve_zero (f g : ℕ → ℝ) : pgConvolve f g 0=f 0*g 0 := by sorry

end ActuarialValuation
