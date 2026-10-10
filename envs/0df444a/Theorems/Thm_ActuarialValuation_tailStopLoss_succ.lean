-- Prove2me | Theorems.Thm_ActuarialValuation_tailStopLoss_succ
-- name    : ActuarialValuation.tailStopLoss_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:39:48.931097+00:00
-- url     : https://prove2.me/theorems/73515227-959a-4c11-9dcd-2c1cc9dab803
-- title:
--   Finite stop-loss and Rockafellar-Uryasev threshold objective: tailStopLoss_succ
-- statement:
--   Truncated tail insurance cost increases by one newly included loss scenario. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   SL_{n+1}=SL_n+(n+1-t)_+p_{n+1}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. Rockafellar and Uryasev, Optimization of Conditional Value-at-Risk (1999 preprint, later Journal of Risk 2000), equation 4 and Theorem 1, page 5, https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf; Rockafellar and Uryasev, Journal of Risk (2000), https://econpapers.repec.org/RePEc:rsk:journ4:2161159. Parent topic: Finite discrete loss distributions, excess-of-loss functionals and Rockafellar-Uryasev conditional value-at-risk auxiliary threshold objective. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailExcess
import Definitions.Def_actuarial_tailStopLoss

namespace ActuarialValuation

theorem tailStopLoss_succ (p : ℕ → ℝ) (n : ℕ) (t : ℝ) : tailStopLoss p (n+1) t = tailStopLoss p n t + tailExcess ((n+1 : ℕ) : ℝ) t * p (n+1) := by sorry

end ActuarialValuation
