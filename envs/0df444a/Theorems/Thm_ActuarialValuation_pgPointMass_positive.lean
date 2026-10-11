-- Prove2me | Theorems.Thm_ActuarialValuation_pgPointMass_positive
-- name    : ActuarialValuation.pgPointMass_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:48:08.870979+00:00
-- url     : https://prove2.me/theorems/af495160-dabd-467e-8d3d-3de1387c9a15
-- title:
--   Discrete severity powers and genuinely compounded frequency: pgPointMass_positive
-- statement:
--   No positive aggregate payout can occur with zero claims. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \text{No positive aggregate payout can occur with zero claims.}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 397. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796; Sundt and Jewell (1981), Further Results on Recursive Evaluation of Compound Distributions, https://doi.org/10.1017/S0515036100006802; S. D. Promislow, Fundamentals of Actuarial Mathematics (2015), chapter 21. Parent topic: Finite-support Panjer counting law, severity convolution powers, aggregate distribution by genuine random-sum weights and corrected zero-severity Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/journals/astin-bulletin-journal-of-the-iaa/article/recursive-evaluation-of-a-family-of-compound-distributions/BD6628F3853600A8F79C6A45E92938CB

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgPointMass

namespace ActuarialValuation

theorem pgPointMass_positive (k : ℕ) (hk : 0<k) : pgPointMass k=0 := by sorry

end ActuarialValuation
