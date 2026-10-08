-- Prove2me | Theorems.Thm_BlackwellDiscreteDP_NearOne_theorem_4c
-- name    : BlackwellDiscreteDP.NearOne.theorem_4c
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:24:08.738973+00:00
-- url     : https://prove2.me/theorems/5edb08a9-6a0f-49c0-9b1c-1d14cbb26437
-- title:
--   Theorem 4(c) — f(s) ∈ E(s, f) always; G(s, f) empty and E(s, f) = {f(s)} for all s ⇒ f optimal
-- statement:
--   In the finite decision model, let $f\in F$ and, for each state $s$, let $E(s,f)$ be the set of actions $a$ for which
--   $$p(s,a)x(f)=x_s(f)\quad\text{and}\quad i(s,a)+p(s,a)y(f)=x_s(f)+y_s(f).$$
--   1. Always $f(s)\in E(s,f)$.
--   2. If, for each $s$, the set $G(s,f)$ of Theorem 4(b) is empty and $E(s,f)$ contains only the point $f(s)$, then $f^{(\infty)}$ is optimal in the sense of §4: there is $\beta_0<1$ such that $f^{(\infty)}$ is β-optimal against all policies for every $\beta\in(\beta_0,1)$.
--
--   This gives a checkable sufficient condition for a stationary policy to be optimal for all discount factors near $1$.
-- source:
--   Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962), DOI 10.1214/aoms/1177704593, p. 723, Theorem 4(c)

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
import Definitions.Def_BlackwellDiscreteDP_NearOne_GainBias
open Filter Topology Matrix

namespace BlackwellDiscreteDP.NearOne

/-- **Theorem 4(c).** For `f ∈ F` and each `s`, let `E(s, f)` be the set of `a` for which
`p(s, a)x(f) = x_s(f)` and `i(s, a) + p(s, a)y(f) = x_s(f) + y_s(f)`. Always `f(s) ∈ E(s, f)`.
If, for each `s`, `G(s, f)` is empty and `E(s, f)` contains only the point `f(s)`, then `f` is
optimal.

Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962),
DOI 10.1214/aoms/1177704593, p. 723, Theorem 4(c).

**Formalization Note.** The parenthetical claim "always `f(s) ∈ E(s, f)`" is the first conjunct.
"Optimal" is the §4 notion `IsOptimal` (β-optimal against all policies for all β in some
interval `(β₀, 1)`), applied to `f^(∞)`. -/
theorem theorem_4c {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
    [Fintype Act] [Nonempty Act] (M : Model St Act)
    (f : St → Act) :
    (∀ s, f s ∈ M.gainBiasEqualSet f s) ∧
      ((∀ s, M.gainBiasImprovementSet f s = ∅) → (∀ s, M.gainBiasEqualSet f s = {f s}) →
        M.IsOptimal (Policy.stationary f)) := by sorry

end BlackwellDiscreteDP.NearOne
