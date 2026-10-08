-- Prove2me | Theorems.Thm_BlackwellDiscreteDP_NearOne_theorem_4b
-- name    : BlackwellDiscreteDP.NearOne.theorem_4b
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:24:36.006997+00:00
-- url     : https://prove2.me/theorems/0c186f81-8a8b-4d72-b494-43889749bf70
-- title:
--   Theorem 4(b) — an improving switch in G(s, f) gives g > f for all β sufficiently near 1
-- statement:
--   In the finite decision model, let $f\in F$ and, for each state $s$, let $G(s,f)$ be the set of actions $a$ for which either
--   $$p(s,a)x(f)>x_s(f)$$
--   or
--   $$p(s,a)x(f)=x_s(f)\quad\text{and}\quad i(s,a)+p(s,a)y(f)>x_s(f)+y_s(f).$$
--   For any $g\in F$ such that $g(s)\in G(s,f)$ for some $s$ and $g(s)=f(s)$ whenever $g(s)\notin G(s,f)$, there is $\beta_0<1$ such that
--   $$V_\beta(g^{(\infty)})>V_\beta(f^{(\infty)})\qquad\text{for all }\beta\in(\beta_0,1),$$
--   in the strict vector order ($\ge$ coordinatewise, and not equal).
--
--   This is the policy improvement step for $\beta=1$: improvement is tested on average income first and on bias second.
-- source:
--   Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962), DOI 10.1214/aoms/1177704593, pp. 722–723, Theorem 4(b)

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
import Definitions.Def_BlackwellDiscreteDP_NearOne_GainBias
open Filter Topology Matrix

namespace BlackwellDiscreteDP.NearOne

/-- **Theorem 4(b).** For `f ∈ F` and each `s`, let `G(s, f)` be the set of `a` for which either
`p(s, a)x(f) > x_s(f)`, or `p(s, a)x(f) = x_s(f)` and `i(s, a) + p(s, a)y(f) > x_s(f) + y_s(f)`.
For any `g` such that `g(s) ∈ G(s, f)` for some `s` and `g(s) = f(s)` whenever `g(s) ∉ G(s, f)`,
`g > f` for all `β` sufficiently near 1.

Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962),
DOI 10.1214/aoms/1177704593, pp. 722–723, Theorem 4(b).

**Formalization Note.** "`g > f`" is `V_β(g^(∞)) > V_β(f^(∞))` in the strict vector order of §2
(`≧` coordinatewise and `≠`), and "for all `β` sufficiently near 1" is: for every `β` in some
interval `(β₀, 1)`, `β₀ < 1`. -/
theorem theorem_4b {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
    [Fintype Act] [Nonempty Act] (M : Model St Act)
    (f g : St → Act) (hG : ∃ s, g s ∈ M.gainBiasImprovementSet f s)
    (hfix : ∀ s, g s ∉ M.gainBiasImprovementSet f s → g s = f s) :
    ∃ β₀ < (1 : ℝ), ∀ β : ℝ, β₀ < β → β < 1 →
      VecGt (M.V β (Policy.stationary g)) (M.V β (Policy.stationary f)) := by sorry

end BlackwellDiscreteDP.NearOne
