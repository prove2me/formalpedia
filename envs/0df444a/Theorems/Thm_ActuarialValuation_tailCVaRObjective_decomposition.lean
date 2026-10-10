-- Prove2me | Theorems.Thm_ActuarialValuation_tailCVaRObjective_decomposition
-- name    : ActuarialValuation.tailCVaRObjective_decomposition
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:42:59.251978+00:00
-- url     : https://prove2.me/theorems/de260e89-d550-4124-a74b-b1318eb57e55
-- title:
--   Finite stop-loss and Rockafellar-Uryasev threshold objective: tailCVaRObjective_decomposition
-- statement:
--   The CVaR auxiliary objective is threshold plus positive excess weighted by the tail fraction. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   F_\alpha=t+SL/(1-\alpha)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. Rockafellar and Uryasev, Optimization of Conditional Value-at-Risk (1999 preprint, later Journal of Risk 2000), equation 4 and Theorem 1, page 5, https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf; Rockafellar and Uryasev, Journal of Risk (2000), https://econpapers.repec.org/RePEc:rsk:journ4:2161159. Parent topic: Finite discrete loss distributions, excess-of-loss functionals and Rockafellar-Uryasev conditional value-at-risk auxiliary threshold objective. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailStopLoss
import Definitions.Def_actuarial_tailCVaRObjective
import Definitions.Def_actuarial_tailUnpaidFraction
import Definitions.Def_actuarial_tailScaledExcess

namespace ActuarialValuation

theorem tailCVaRObjective_decomposition (p : ℕ → ℝ) (n : ℕ) (a t : ℝ) : tailCVaRObjective p n a t = t + tailScaledExcess (tailStopLoss p n t) (tailUnpaidFraction a) := by sorry

end ActuarialValuation
