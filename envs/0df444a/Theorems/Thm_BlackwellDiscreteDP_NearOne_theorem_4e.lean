-- Prove2me | Theorems.Thm_BlackwellDiscreteDP_NearOne_theorem_4e
-- name    : BlackwellDiscreteDP.NearOne.theorem_4e
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:24:42.67072+00:00
-- url     : https://prove2.me/theorems/e3e79e84-6686-4463-a52a-bcd195f3ecbe
-- title:
--   Theorem 4(e) — the nearly optimal g are exactly those with x(g) = x(f*) and y(g) = y(f*)
-- statement:
--   In the finite decision model, let $f_0\in F$ be such that $G(s,f_0)$ is empty for every state $s$. Then:
--   1. $x(f_0)\ge x(g)$ for all $g\in F$.
--   2. Let $F^*$ be the set of all $g\in F$ with $x(g)=x(f_0)$. There is $f^*\in F^*$ with $y(f^*)\ge y(g)$ for all $g\in F^*$.
--   3. The nearly optimal $g\in F$ are exactly those for which
--   $$x(g)=x(f^*)\quad\text{and}\quad y(g)=y(f^*).$$
--
--   Inequalities between vectors are coordinatewise, and "$g$ is nearly optimal" means that the stationary policy $g^{(\infty)}$ satisfies $U(\beta)-V_\beta(g^{(\infty)})\to0$ as $\beta\to1$. The theorem characterizes near optimality as the lexicographic maximization of average income and then bias.
--
--   **Formalization Note** The three assertions form one statement, so that the $f^*$ of the third is the $f^*$ of the second. Near optimality is compared against all policies and stated without $U$, as in Theorem 4(d).
-- source:
--   Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962), DOI 10.1214/aoms/1177704593, p. 723, Theorem 4(e)

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
import Definitions.Def_BlackwellDiscreteDP_NearOne_GainBias
open Filter Topology Matrix

namespace BlackwellDiscreteDP.NearOne

/-- **Theorem 4(e).** For any `f₀` for which `G(s, f₀)` is empty for all `s`, `x(f₀) ≧ x(g)` for
all `g`. Denote by `F*` the set of all `g` such that `x(g) = x(f₀)`. There is an `f* ∈ F*` with
`y(f*) ≧ y(g)` for all `g ∈ F*`. The nearly optimal `g`'s are exactly those for which
`x(g) = x(f*)` and `y(g) = y(f*)`.

Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962),
DOI 10.1214/aoms/1177704593, p. 723, Theorem 4(e).

**Formalization Note.** All three assertions are in one statement so that the `f*` of the third
is the `f*` of the second. `≧` is coordinatewise; `g` ranges over all decision rules `F`; a rule
`g` is "nearly optimal" when the stationary policy `g^(∞)` is (`IsNearlyOptimal`, the §4 notion,
against all policies). -/
theorem theorem_4e {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
    [Fintype Act] [Nonempty Act] (M : Model St Act)
    (f₀ : St → Act) (hG : ∀ s, M.gainBiasImprovementSet f₀ s = ∅) :
    (∀ g : St → Act, M.x g ≤ M.x f₀) ∧
      ∃ fstar : St → Act, M.x fstar = M.x f₀ ∧
        (∀ g : St → Act, M.x g = M.x f₀ → M.y g ≤ M.y fstar) ∧
        ∀ g : St → Act,
          (M.IsNearlyOptimal (Policy.stationary g) ↔ M.x g = M.x fstar ∧ M.y g = M.y fstar) := by sorry

end BlackwellDiscreteDP.NearOne
