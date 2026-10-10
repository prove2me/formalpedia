-- Prove2me | Theorems.Thm_ActuarialValuation_tailStopLoss_zero_weights
-- name    : ActuarialValuation.tailStopLoss_zero_weights
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:40:09.534771+00:00
-- url     : https://prove2.me/theorems/f110ac22-5ba7-489a-b420-82b23ffa7d95
-- title:
--   Finite stop-loss and Rockafellar-Uryasev threshold objective: tailStopLoss_zero_weights
-- statement:
--   If all loss probabilities are zero the finite expected ceded amount is zero. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   SL(0)=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. Rockafellar and Uryasev, Optimization of Conditional Value-at-Risk (1999 preprint, later Journal of Risk 2000), equation 4 and Theorem 1, page 5, https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf; Rockafellar and Uryasev, Journal of Risk (2000), https://econpapers.repec.org/RePEc:rsk:journ4:2161159. Parent topic: Finite discrete loss distributions, excess-of-loss functionals and Rockafellar-Uryasev conditional value-at-risk auxiliary threshold objective. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailStopLoss

namespace ActuarialValuation

theorem tailStopLoss_zero_weights (n : ℕ) (t : ℝ) : tailStopLoss (fun _ => (0 : ℝ)) n t = 0 := by sorry

end ActuarialValuation
