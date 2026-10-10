-- Prove2me | Theorems.Thm_ActuarialValuation_tailExcess_mono_loss
-- name    : ActuarialValuation.tailExcess_mono_loss
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:32:53.623575+00:00
-- url     : https://prove2.me/theorems/424b50b0-2a1f-4ea7-b0f0-46aad7ea893f
-- title:
--   Finite scenario probabilities, losses and positive-part payouts: tailExcess_mono_loss
-- statement:
--   Higher losses cannot lower ceded payment at fixed retention. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   x\le y\Rightarrow(x-t)_+\le(y-t)_+
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. Rockafellar and Uryasev, Optimization of Conditional Value-at-Risk (1999 preprint, later Journal of Risk 2000), equation 4 and Theorem 1, page 5, https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf; Rockafellar and Uryasev, Journal of Risk (2000), https://econpapers.repec.org/RePEc:rsk:journ4:2161159. Parent topic: Finite discrete loss distributions, excess-of-loss functionals and Rockafellar-Uryasev conditional value-at-risk auxiliary threshold objective. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailExcess

namespace ActuarialValuation

theorem tailExcess_mono_loss (x y t : ℝ) (h : x ≤ y) : tailExcess x t ≤ tailExcess y t := by sorry

end ActuarialValuation
