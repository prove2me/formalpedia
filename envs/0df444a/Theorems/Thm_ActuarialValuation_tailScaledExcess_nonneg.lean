-- Prove2me | Theorems.Thm_ActuarialValuation_tailScaledExcess_nonneg
-- name    : ActuarialValuation.tailScaledExcess_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:44:17.417042+00:00
-- url     : https://prove2.me/theorems/fe6aca8c-de19-4b65-b8c5-dcc2d686b8e2
-- title:
--   Finite stop-loss and Rockafellar-Uryasev threshold objective: tailScaledExcess_nonneg
-- statement:
--   Nonnegative expected excess and positive tail mass make a valid nonnegative scaling. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   SL\ge0,\tau>0\Rightarrow K\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. Rockafellar and Uryasev, Optimization of Conditional Value-at-Risk (1999 preprint, later Journal of Risk 2000), equation 4 and Theorem 1, page 5, https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf; Rockafellar and Uryasev, Journal of Risk (2000), https://econpapers.repec.org/RePEc:rsk:journ4:2161159. Parent topic: Finite discrete loss distributions, excess-of-loss functionals and Rockafellar-Uryasev conditional value-at-risk auxiliary threshold objective. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailScaledExcess

namespace ActuarialValuation

theorem tailScaledExcess_nonneg (excess frac : ℝ) (he : 0 ≤ excess) (hf : 0 < frac) : 0 ≤ tailScaledExcess excess frac := by sorry

end ActuarialValuation
