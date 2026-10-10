-- Prove2me | Theorems.Thm_ActuarialValuation_tailStopLoss_zero
-- name    : ActuarialValuation.tailStopLoss_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:33:20.295081+00:00
-- url     : https://prove2.me/theorems/03fd9b64-13b5-4e9e-8769-585a53c639bc
-- title:
--   Finite stop-loss and Rockafellar-Uryasev threshold objective: tailStopLoss_zero
-- statement:
--   A nonnegative threshold leaves zero expected payout when the only included claim loss is zero. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   SL_0(t)=0\text{ for }t\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. Rockafellar and Uryasev, Optimization of Conditional Value-at-Risk (1999 preprint, later Journal of Risk 2000), equation 4 and Theorem 1, page 5, https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf; Rockafellar and Uryasev, Journal of Risk (2000), https://econpapers.repec.org/RePEc:rsk:journ4:2161159. Parent topic: Finite discrete loss distributions, excess-of-loss functionals and Rockafellar-Uryasev conditional value-at-risk auxiliary threshold objective. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailStopLoss

namespace ActuarialValuation

theorem tailStopLoss_zero (p : ℕ → ℝ) (t : ℝ) (ht : 0 ≤ t) : tailStopLoss p 0 t = 0 := by sorry

end ActuarialValuation
