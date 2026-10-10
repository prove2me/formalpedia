-- Prove2me | Theorems.Thm_ActuarialValuation_tailLossMean_succ
-- name    : ActuarialValuation.tailLossMean_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:30:30.419736+00:00
-- url     : https://prove2.me/theorems/afc6b4f7-cd38-4852-8190-57f62bfaaea5
-- title:
--   Finite scenario probabilities, losses and positive-part payouts: tailLossMean_succ
-- statement:
--   Each extra loss lattice point adds probability-weighted claim amount. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \mu_{n+1}=\mu_n+(n+1)p_{n+1}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. Rockafellar and Uryasev, Optimization of Conditional Value-at-Risk (1999 preprint, later Journal of Risk 2000), equation 4 and Theorem 1, page 5, https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf; Rockafellar and Uryasev, Journal of Risk (2000), https://econpapers.repec.org/RePEc:rsk:journ4:2161159. Parent topic: Finite discrete loss distributions, excess-of-loss functionals and Rockafellar-Uryasev conditional value-at-risk auxiliary threshold objective. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailLossMean

namespace ActuarialValuation

theorem tailLossMean_succ (p : ℕ → ℝ) (n : ℕ) : tailLossMean p (n+1) = tailLossMean p n + ((n+1 : ℕ) : ℝ) * p (n+1) := by sorry

end ActuarialValuation
