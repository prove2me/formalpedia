-- Prove2me | Theorems.Thm_ActuarialValuation_tailMass_succ
-- name    : ActuarialValuation.tailMass_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:29:15.030868+00:00
-- url     : https://prove2.me/theorems/a761dc66-5245-4e64-a30c-eb8933239faf
-- title:
--   Finite scenario probabilities, losses and positive-part payouts: tailMass_succ
-- statement:
--   A newly included loss scenario adds its own probability. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   M_{n+1}=M_n+p_{n+1}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. Rockafellar and Uryasev, Optimization of Conditional Value-at-Risk (1999 preprint, later Journal of Risk 2000), equation 4 and Theorem 1, page 5, https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf; Rockafellar and Uryasev, Journal of Risk (2000), https://econpapers.repec.org/RePEc:rsk:journ4:2161159. Parent topic: Finite discrete loss distributions, excess-of-loss functionals and Rockafellar-Uryasev conditional value-at-risk auxiliary threshold objective. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailMass

namespace ActuarialValuation

theorem tailMass_succ (p : ℕ → ℝ) (n : ℕ) : tailMass p (n+1) = tailMass p n + p (n+1) := by sorry

end ActuarialValuation
