-- Prove2me | Theorems.Thm_ActuarialValuation_tailUpperMass_zero_range
-- name    : ActuarialValuation.tailUpperMass_zero_range
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:46:48.186406+00:00
-- url     : https://prove2.me/theorems/82638762-9fcf-48d1-8543-81032478875d
-- title:
--   Discrete cumulative tails, thresholds and monetary shifts: tailUpperMass_zero_range
-- statement:
--   There is no strictly positive lattice loss in a zero-loss-only truncation. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   U_0(0)=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. Rockafellar and Uryasev, Optimization of Conditional Value-at-Risk (1999 preprint, later Journal of Risk 2000), equation 4 and Theorem 1, page 5, https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf; Rockafellar and Uryasev, Journal of Risk (2000), https://econpapers.repec.org/RePEc:rsk:journ4:2161159. Parent topic: Finite discrete loss distributions, excess-of-loss functionals and Rockafellar-Uryasev conditional value-at-risk auxiliary threshold objective. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailUpperMass

namespace ActuarialValuation

theorem tailUpperMass_zero_range (p : ℕ → ℝ) : tailUpperMass p 0 0 = 0 := by sorry

end ActuarialValuation
