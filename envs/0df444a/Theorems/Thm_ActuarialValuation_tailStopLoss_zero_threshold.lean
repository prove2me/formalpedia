-- Prove2me | Theorems.Thm_ActuarialValuation_tailStopLoss_zero_threshold
-- name    : ActuarialValuation.tailStopLoss_zero_threshold
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:48:16.2299+00:00
-- url     : https://prove2.me/theorems/5b7c41da-2018-4e7d-8a75-3f236a839c18
-- title:
--   Discrete cumulative tails, thresholds and monetary shifts: tailStopLoss_zero_threshold
-- statement:
--   With zero deductible, the expected insured payout equals finite expected claim loss. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   SL_n(0)=E[X]
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. Rockafellar and Uryasev, Optimization of Conditional Value-at-Risk (1999 preprint, later Journal of Risk 2000), equation 4 and Theorem 1, page 5, https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf; Rockafellar and Uryasev, Journal of Risk (2000), https://econpapers.repec.org/RePEc:rsk:journ4:2161159. Parent topic: Finite discrete loss distributions, excess-of-loss functionals and Rockafellar-Uryasev conditional value-at-risk auxiliary threshold objective. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailLossMean
import Definitions.Def_actuarial_tailStopLoss

namespace ActuarialValuation

theorem tailStopLoss_zero_threshold (p : ℕ → ℝ) (n : ℕ) : tailStopLoss p n 0 = tailLossMean p n := by sorry

end ActuarialValuation
