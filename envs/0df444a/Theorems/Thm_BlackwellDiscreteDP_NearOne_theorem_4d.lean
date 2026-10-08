-- Prove2me | Theorems.Thm_BlackwellDiscreteDP_NearOne_theorem_4d
-- name    : BlackwellDiscreteDP.NearOne.theorem_4d
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:24:26.963291+00:00
-- url     : https://prove2.me/theorems/ed1d315c-82f0-4bc1-b7b3-caa6ee3d04ed
-- title:
--   Theorem 4(d) — G(s, f) empty for all s and [g(s) ∈ E(s, f) ∀ s ⇒ Q*(g)Q*(f) = Q*(g)] ⇒ f nearly optimal
-- statement:
--   In the finite decision model, let $f\in F$ satisfy
--   1. $G(s,f)$ is empty for each state $s$, and
--   2. for every $g\in F$, if $g(s)\in E(s,f)$ for all $s$, then $Q^*(g)Q^*(f)=Q^*(g)$.
--
--   Then $f^{(\infty)}$ is nearly optimal: $U(\beta)-V_\beta(f^{(\infty)})\to0$ as $\beta\to1$, where $U(\beta)$ is the return of a β-optimal policy.
--
--   This identifies a nearly optimal stationary policy at the point where the $\beta=1$ improvement routine stops, under a condition on limit matrices that holds, for instance, when there is a single absorbing state reached under every policy.
--
--   **Formalization Note** Near optimality is stated without $U$: for every $\varepsilon>0$ there is $\beta_0<1$ such that for all $\beta\in(\beta_0,1)$, every policy $\pi$ and every state $s$, $V_\beta(\pi)_s\le V_\beta(f^{(\infty)})_s+\varepsilon$.
-- source:
--   Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962), DOI 10.1214/aoms/1177704593, p. 723, Theorem 4(d)

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
import Definitions.Def_BlackwellDiscreteDP_NearOne_GainBias
open Filter Topology Matrix

namespace BlackwellDiscreteDP.NearOne

/-- **Theorem 4(d).** If for each `s`, `G(s, f)` is empty, and `g(s) ∈ E(s, f)` for all `s`
implies `Q*(g)Q*(f) = Q*(g)`, then `f` is nearly optimal.

Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962),
DOI 10.1214/aoms/1177704593, p. 723, Theorem 4(d).

**Formalization Note.** The second hypothesis ranges over all decision rules `g ∈ F`. "Nearly
optimal" is the §4 notion `IsNearlyOptimal` (`U(β) − V_β → 0`, encoded without `U`, against all
policies), applied to `f^(∞)`. -/
theorem theorem_4d {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
    [Fintype Act] [Nonempty Act] (M : Model St Act)
    (f : St → Act) (hG : ∀ s, M.gainBiasImprovementSet f s = ∅)
    (hE : ∀ g : St → Act, (∀ s, g s ∈ M.gainBiasEqualSet f s) →
      M.Qstar g * M.Qstar f = M.Qstar g) :
    M.IsNearlyOptimal (Policy.stationary f) := by sorry

end BlackwellDiscreteDP.NearOne
