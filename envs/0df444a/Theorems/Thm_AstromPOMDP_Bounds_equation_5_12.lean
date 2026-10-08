-- Prove2me | Theorems.Thm_AstromPOMDP_Bounds_equation_5_12
-- name    : AstromPOMDP.Bounds.equation_5_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:27:16.730291+00:00
-- url     : https://prove2.me/theorems/1791f2e5-1a20-46fc-8934-9e6336e495d4
-- title:
--   Equation (5.12) — the minimal loss lies between complete-information and open-loop values
-- statement:
--   For every finite partially observed control model satisfying the standing conditions of §II, let $\mathrm{OPT}$ be the infimum of the original expected loss (2.6) over all admissible laws that use output histories. Let $V$, $V'$ and $V''$ be respectively the partial-observation, complete-information and open-loop backward values. With $w(1)$ the posterior after the first output $\eta_1$,
--   $$\mathrm{OPT}=\mathbb E_{\eta_1}[V_1(w(1))],\qquad \mathbb E_{\eta_1}[V'_1(w(1))]\le\mathrm{OPT}\le\mathbb E_{\eta_1}[V''_1(w(1))].$$
--
--   Thus the cost achievable with incomplete measurements lies between the ideal cost with exact state observations and the cost of a control schedule that ignores observations. The equality ties the bounds to the minimal loss of P.1, as identified in Theorem 2.
--
--   **Formalization Note** The expectation is a finite sum over the first output. The three value functions are defined by backward recursion and not supplied as unrelated variables.
-- source:
--   Åström, Optimal Control of Markov Processes with Incomplete State Information, J. Math. Anal. Appl. 10(1):174–205 (1965), https://doi.org/10.1016/0022-247X(65)90154-X, p. 193, §V, (5.12), with Theorem 2 (3.29), p. 185

import Definitions.Def_AstromPOMDP_Bounds_Model

namespace AstromPOMDP.Bounds

variable {St Obs : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
  [Fintype Obs] [DecidableEq Obs] [Nonempty Obs]
  {d N : ℕ} [NeZero N]

/-- Åström, *Optimal Control of Markov Processes with Incomplete State Information*,
J. Math. Anal. Appl. 10 (1965), §V, (5.12), p. 193, together with the
identification of P.1's minimal value in Theorem 2, (3.29), p. 185.

`optimalCost` ranges over all admissible observation-history policies and is
computed from the joint path law (2.6). The bounds are finite expectations
over the first output; `Vprime` is complete information and `Vdouble` is an
open-loop control schedule. -/
theorem equation_5_12 (m : Model St Obs d N) :
    optimalCost m = firstExpectation m (V m 1) ∧
    firstExpectation m (Vprime m 1) ≤ optimalCost m ∧
    optimalCost m ≤ firstExpectation m (Vdouble m 1) := by sorry

end AstromPOMDP.Bounds
