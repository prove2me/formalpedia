-- Prove2me | Theorems.Thm_ActuarialValuation_tailCDF_nonneg
-- name    : ActuarialValuation.tailCDF_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:47:10.962819+00:00
-- url     : https://prove2.me/theorems/ec6766ce-274e-4881-8eb4-d1c3d9fd1026
-- title:
--   Discrete cumulative tails, thresholds and monetary shifts: tailCDF_nonneg
-- statement:
--   Every included lower tail contribution is nonnegative. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   p_k\ge0\Rightarrow F_n(t)\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. Rockafellar and Uryasev, Optimization of Conditional Value-at-Risk (1999 preprint, later Journal of Risk 2000), equation 4 and Theorem 1, page 5, https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf; Rockafellar and Uryasev, Journal of Risk (2000), https://econpapers.repec.org/RePEc:rsk:journ4:2161159. Parent topic: Finite discrete loss distributions, excess-of-loss functionals and Rockafellar-Uryasev conditional value-at-risk auxiliary threshold objective. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailCDF

namespace ActuarialValuation

theorem tailCDF_nonneg (p : ℕ → ℝ) (n t : ℕ) (hp : ∀ k ∈ Finset.range (n+1), 0 ≤ p k) : 0 ≤ tailCDF p n t := by sorry

end ActuarialValuation
