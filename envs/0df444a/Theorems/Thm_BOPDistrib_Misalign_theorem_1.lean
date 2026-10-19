-- Prove2me | Theorems.Thm_BOPDistrib_Misalign_theorem_1
-- name    : BOPDistrib.Misalign.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:17.763592+00:00
-- url     : https://prove2.me/theorems/b0681d13-1933-4f06-bdc5-0d1387e0cce3
-- title:
--   Theorem 1, p. 15 (PDF 16), proof pp. 38–40 — F/M are optimal under pricing (a), FR/MR under pricing (b)
-- statement:
--   Fix the parameters and an ATP $m$ satisfying the standing assumptions (in particular the strict homogeneous Assumption 1). The four allocations of Theorem 1 are feasible, and each pricing regime is solved by two of them.
--
--   1. Under pricing strategy (a), the F and M allocations are feasible, and
--   $$\max\{\Pi^a_D(x,\theta): (x,\theta)\ \text{feasible for (a)}\}=\max(\Pi^F,\Pi^M),$$
--   with the maximum attained.
--   2. Under pricing strategy (b), for every risk aversion $\alpha>0$, the FR and MR allocations are feasible, and
--   $$\max\{\Pi^b_D(x,\theta): (x,\theta)\ \text{feasible for (b)}\}=\max(\Pi^{FR},\Pi^{MR}).$$
--
--   Feasibility for (a) means $\theta_0\le\theta\le1$, $0\le x\le v_h-m$ and $c_\theta(\theta-\theta_0)+x\theta\beta\le b$. For (b), the demand $\theta\beta$ is replaced by $\beta+(1-\theta)(1-\beta)$.
--
--   Together these give the paper's conclusion $\Pi^{OPT}_D=\max(\Pi^F_D,\Pi^M_D,\Pi^{FR}_D,\Pi^{MR}_D)$. They justify reading "strategy $i$ is optimal" as $\Pi^i$ being the largest of the four values.
--
--   **Formalization Note** Each pricing regime is optimized under its own demand in the budget, as the proof of Theorem 1 does. The strategy values are the pricing outcomes evaluated at the allocations.
-- source:
--   Calmon, Jue-Rajasingh, Romero & Stenson, Operational strategies for distributing durable goods in the base of the pyramid, accepted manuscript (M&SOM 24(4), 2022; TSpace, SSRN 2882402), p. 15 (PDF 16), Theorem 1; pp. 38–40 (PDF 39–41), proof of Theorem 1

import Mathlib
import Definitions.Def_BOPDistrib_Misalign_Model

namespace BOPDistrib.Misalign

/-- Theorem 1 (p. 15) in regime form, with the allocations of its proof (pp. 38–40): under pricing
strategy (a) the allocations of F and M are feasible and the better of the two is optimal over all
feasible allocations; under pricing strategy (b), for every risk aversion `α > 0`, the same holds for
FR and MR. Each regime is optimized under its own demand, as in the proof. -/
theorem theorem_1 (P : Params) (m : ℝ) (hS : Standing P m) :
    FeasA P m (xF P m) (thetaF P m) ∧ FeasA P m (xM P) (thetaM P) ∧
      IsGreatest {v | ∃ x θ, FeasA P m x θ ∧ v = PiA P m x θ} (max (PiF P m) (PiM P m)) ∧
      ∀ α : ℝ, 0 < α →
        FeasB P m (xFR P m) (thetaFR P m α) ∧ FeasB P m (xMR P) (thetaMR P) ∧
          IsGreatest {v | ∃ x θ, FeasB P m x θ ∧ v = PiB P m α x θ}
            (max (PiFR P m α) (PiMR P m α)) := by sorry

end BOPDistrib.Misalign
