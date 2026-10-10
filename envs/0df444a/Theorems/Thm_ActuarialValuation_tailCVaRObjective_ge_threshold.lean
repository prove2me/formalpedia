-- Prove2me | Theorems.Thm_ActuarialValuation_tailCVaRObjective_ge_threshold
-- name    : ActuarialValuation.tailCVaRObjective_ge_threshold
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:43:38.450568+00:00
-- url     : https://prove2.me/theorems/d435d958-37ad-48d2-b9ef-21a6477ef0e5
-- title:
--   Finite stop-loss and Rockafellar-Uryasev threshold objective: tailCVaRObjective_ge_threshold
-- statement:
--   The finite CVaR objective is at least its risk threshold when the expected excess is nonnegative. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   F_\alpha(t)\ge t
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. Rockafellar and Uryasev, Optimization of Conditional Value-at-Risk (1999 preprint, later Journal of Risk 2000), equation 4 and Theorem 1, page 5, https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf; Rockafellar and Uryasev, Journal of Risk (2000), https://econpapers.repec.org/RePEc:rsk:journ4:2161159. Parent topic: Finite discrete loss distributions, excess-of-loss functionals and Rockafellar-Uryasev conditional value-at-risk auxiliary threshold objective. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailCVaRObjective

namespace ActuarialValuation

theorem tailCVaRObjective_ge_threshold (p : ℕ → ℝ) (n : ℕ) (a t : ℝ) (ha : a < 1) (hp : ∀ k ∈ Finset.range (n+1), 0 ≤ p k) : t ≤ tailCVaRObjective p n a t := by sorry

end ActuarialValuation
