-- Prove2me | Theorems.Thm_ActuarialValuation_tailCDF_partition
-- name    : ActuarialValuation.tailCDF_partition
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:46:59.067737+00:00
-- url     : https://prove2.me/theorems/f21fe9c5-d206-4dfb-9304-a6e81e7645aa
-- title:
--   Discrete cumulative tails, thresholds and monetary shifts: tailCDF_partition
-- statement:
--   Lower and strictly upper discrete mass form a disjoint partition of truncated loss scenarios. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   F_n(t)+U_n(t)=M_n
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. Rockafellar and Uryasev, Optimization of Conditional Value-at-Risk (1999 preprint, later Journal of Risk 2000), equation 4 and Theorem 1, page 5, https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf; Rockafellar and Uryasev, Journal of Risk (2000), https://econpapers.repec.org/RePEc:rsk:journ4:2161159. Parent topic: Finite discrete loss distributions, excess-of-loss functionals and Rockafellar-Uryasev conditional value-at-risk auxiliary threshold objective. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailMass
import Definitions.Def_actuarial_tailCDF
import Definitions.Def_actuarial_tailUpperMass

namespace ActuarialValuation

theorem tailCDF_partition (p : ℕ → ℝ) (n t : ℕ) : tailCDF p n t + tailUpperMass p n t = tailMass p n := by sorry

end ActuarialValuation
