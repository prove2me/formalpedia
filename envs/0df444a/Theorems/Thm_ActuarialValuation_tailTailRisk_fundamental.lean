-- Prove2me | Theorems.Thm_ActuarialValuation_tailTailRisk_fundamental
-- name    : ActuarialValuation.tailTailRisk_fundamental
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:48:33.256447+00:00
-- url     : https://prove2.me/theorems/4d55a2d8-b255-4812-9e82-ca170ebca467
-- title:
--   Discrete cumulative tails, thresholds and monetary shifts: tailTailRisk_fundamental
-- statement:
--   The root joins tail-stop-loss nonnegativity, a valid finite CVaR objective, monetary translation equivalence and the complete lower/upper finite loss partition. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   SL(t)\ge0,\;F_\alpha(t)\ge t,\;F_\alpha^{X+s}(t+s)=F_\alpha^X(t)+s
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. Rockafellar and Uryasev, Optimization of Conditional Value-at-Risk (1999 preprint, later Journal of Risk 2000), equation 4 and Theorem 1, page 5, https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf; Rockafellar and Uryasev, Journal of Risk (2000), https://econpapers.repec.org/RePEc:rsk:journ4:2161159. Parent topic: Finite discrete loss distributions, excess-of-loss functionals and Rockafellar-Uryasev conditional value-at-risk auxiliary threshold objective. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailMass
import Definitions.Def_actuarial_tailLossMean
import Definitions.Def_actuarial_tailStopLoss
import Definitions.Def_actuarial_tailCVaRObjective
import Definitions.Def_actuarial_tailCDF
import Definitions.Def_actuarial_tailUpperMass
import Definitions.Def_actuarial_tailShiftObjective

namespace ActuarialValuation

theorem tailTailRisk_fundamental (p : ℕ → ℝ) (n : ℕ) (a t s : ℝ) (ha : a < 1) (hp : ∀ k ∈ Finset.range (n+1), 0 ≤ p k) : (0 ≤ tailStopLoss p n t) ∧ (t ≤ tailCVaRObjective p n a t) ∧ (tailShiftObjective p n a t s = tailCVaRObjective p n a t + s) ∧ (tailCDF p n n + tailUpperMass p n n = tailMass p n) ∧ (tailStopLoss p n 0 = tailLossMean p n) := by sorry

end ActuarialValuation
