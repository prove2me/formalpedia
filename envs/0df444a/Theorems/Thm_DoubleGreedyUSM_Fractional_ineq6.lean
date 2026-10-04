-- Prove2me | Theorems.Thm_DoubleGreedyUSM_Fractional_ineq6
-- name    : DoubleGreedyUSM.Fractional.ineq6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:05:14.354168+00:00
-- url     : https://prove2.me/theorems/8232d263-6f3d-4fba-8743-c145db8e58f5
-- title:
--   Proof of Lemma A.2, Case 3, (6) — $F(OPT_{i-1}) - F(OPT_i) \le a_i b_i/(a_i+b_i)$
-- statement:
--   Let $f : 2^{\mathcal N} \to \mathbb R$ be submodular with multilinear extension $F$, let $OPT$ be an optimal solution, and run Algorithm 4 on $f$ in an order $u_1, \dots, u_n$ of the ground set, with $OPT_i = (OPT \vee x_i) \wedge y_i$. At an iteration $1 \le i \le n$ with $a_i \ge 0$ and $b_i > 0$ (Case 3 of the proof of Lemma A.2), where $a_i = F(x_{i-1} + \{u_i\}) - F(x_{i-1})$ and $b_i = F(y_{i-1} - \{u_i\}) - F(y_{i-1})$,
--   $$F(OPT_{i-1}) - F(OPT_i) \le \frac{a_i b_i}{a_i + b_i},$$
--   whether or not $u_i \in OPT$.
--
--   This bounds the loss of the reference point $OPT_i$ in the step where both solutions move; combined with (4) and (5) it reduces Lemma A.2 in this case to $\frac{a_i b_i}{a_i + b_i} \le \frac12 \cdot \frac{a_i^2 + b_i^2}{a_i + b_i}$.
--
--   **Formalization Note.** The page writes out the case $u_i \notin OPT$ and says "the proof for the other case is similar"; Lemma A.2 needs both, so the statement has no hypothesis on whether $u_i \in OPT$. Nonnegativity of $f$ is not assumed.
-- source:
--   Buchbinder, Feldman, Naor, Schwartz, A Tight Linear Time (1/2)-Approximation for Unconstrained Submodular Maximization, FOCS 2012 version, proof of Lemma A.2, Case 3, inequality (6) (PDF p. 10)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_DoubleGreedyUSM_Fractional_Algorithm4

namespace DoubleGreedyUSM.Fractional

/-- Proof of Lemma A.2, Case 3, inequality (6) (PDF p. 10), for both `u_i ∉ OPT` (the case the
page writes out) and `u_i ∈ OPT` ("the proof for the other case is similar"): at an iteration `i`
of Algorithm 4 run on a submodular `f` in the order `l` of the ground set, with `a_i ≥ 0` and
`b_i > 0`, `F(OPT_{i−1}) − F(OPT_i) ≤ a_i b_i / (a_i + b_i)`. -/
theorem ineq6 {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f)
    (l : List X) (hl : l.Nodup) (hcov : ∀ x, x ∈ l)
    (O : Finset X) (hO : ∀ S : Finset X, f S ≤ f O)
    (i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ l.length)
    (ha : 0 ≤ aGain f (state f l (i - 1)).1 (l[i - 1]'(by omega)))
    (hb : 0 < bGain f (state f l (i - 1)).2 (l[i - 1]'(by omega))) :
    NonmonotoneSubmod.Shared.F f (optI O (state f l (i - 1)))
        - NonmonotoneSubmod.Shared.F f (optI O (state f l i))
      ≤ aGain f (state f l (i - 1)).1 (l[i - 1]'(by omega))
          * bGain f (state f l (i - 1)).2 (l[i - 1]'(by omega))
        / (aGain f (state f l (i - 1)).1 (l[i - 1]'(by omega))
            + bGain f (state f l (i - 1)).2 (l[i - 1]'(by omega))) := by sorry

end DoubleGreedyUSM.Fractional
