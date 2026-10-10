-- Prove2me | Theorems.Thm_ActuarialValuation_tailShiftObjective_translation
-- name    : ActuarialValuation.tailShiftObjective_translation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:47:49.842091+00:00
-- url     : https://prove2.me/theorems/750691ad-8078-4c66-bdba-43ff0bf626dc
-- title:
--   Discrete cumulative tails, thresholds and monetary shifts: tailShiftObjective_translation
-- statement:
--   The CVaR threshold objective is translation equivariant under uniform monetary shift. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   F^{X+s}_\alpha(t+s)=F^X_\alpha(t)+s
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. Rockafellar and Uryasev, Optimization of Conditional Value-at-Risk (1999 preprint, later Journal of Risk 2000), equation 4 and Theorem 1, page 5, https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf; Rockafellar and Uryasev, Journal of Risk (2000), https://econpapers.repec.org/RePEc:rsk:journ4:2161159. Parent topic: Finite discrete loss distributions, excess-of-loss functionals and Rockafellar-Uryasev conditional value-at-risk auxiliary threshold objective. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailCVaRObjective
import Definitions.Def_actuarial_tailShiftObjective

namespace ActuarialValuation

theorem tailShiftObjective_translation (p : ℕ → ℝ) (n : ℕ) (a t s : ℝ) : tailShiftObjective p n a t s = tailCVaRObjective p n a t + s := by sorry

end ActuarialValuation
