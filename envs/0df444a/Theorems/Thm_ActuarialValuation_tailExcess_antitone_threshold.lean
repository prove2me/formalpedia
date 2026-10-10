-- Prove2me | Theorems.Thm_ActuarialValuation_tailExcess_antitone_threshold
-- name    : ActuarialValuation.tailExcess_antitone_threshold
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:33:02.003755+00:00
-- url     : https://prove2.me/theorems/89fa2129-c609-4fa9-8896-1992a96c9608
-- title:
--   Finite scenario probabilities, losses and positive-part payouts: tailExcess_antitone_threshold
-- statement:
--   Increasing retention cannot increase payment for any insured loss. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   t\le u\Rightarrow(x-u)_+\le(x-t)_+
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. Rockafellar and Uryasev, Optimization of Conditional Value-at-Risk (1999 preprint, later Journal of Risk 2000), equation 4 and Theorem 1, page 5, https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf; Rockafellar and Uryasev, Journal of Risk (2000), https://econpapers.repec.org/RePEc:rsk:journ4:2161159. Parent topic: Finite discrete loss distributions, excess-of-loss functionals and Rockafellar-Uryasev conditional value-at-risk auxiliary threshold objective. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailExcess

namespace ActuarialValuation

theorem tailExcess_antitone_threshold (x t u : ℝ) (h : t ≤ u) : tailExcess x u ≤ tailExcess x t := by sorry

end ActuarialValuation
