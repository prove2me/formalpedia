-- Prove2me | Theorems.Thm_DoubleGreedyUSM_Fractional_telescoped
-- name    : DoubleGreedyUSM.Fractional.telescoped
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:05:39.064513+00:00
-- url     : https://prove2.me/theorems/c07e6001-38dd-40da-ad34-59268da9dab1
-- title:
--   Proof of Theorem A.1, telescoped display — $F(OPT_0) - F(OPT_n) \le (F(x_n) + F(y_n))/2$
-- statement:
--   Let $f : 2^{\mathcal N} \to \mathbb R$ be nonnegative and submodular with multilinear extension $F$, let $OPT$ be an optimal solution, and run Algorithm 4 on $f$ in an order $u_1, \dots, u_n$ of the ground set, with $OPT_i = (OPT \vee x_i) \wedge y_i$. Then
--   $$F(OPT_0) - F(OPT_n) \le \frac12 \bigl[F(x_n) - F(x_0)\bigr] + \frac12 \bigl[F(y_n) - F(y_0)\bigr] \le \frac{F(x_n) + F(y_n)}{2}.$$
--
--   The first inequality is the sum of Lemma A.2 over $i = 1, \dots, n$ after telescoping; the second uses $F(x_0) = f(\emptyset) \ge 0$ and $F(y_0) = f(\mathcal N) \ge 0$. With $OPT_0 = OPT$ and $OPT_n = x_n = y_n$ it yields Theorem A.1.
--
--   **Formalization Note.** Both inequalities are stated as a conjunction. The order is a duplicate-free list containing every element of the finite type $X$, and $n$ is its length.
-- source:
--   Buchbinder, Feldman, Naor, Schwartz, A Tight Linear Time (1/2)-Approximation for Unconstrained Submodular Maximization, FOCS 2012 version, proof of Theorem A.1, second display (PDF p. 9)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_DoubleGreedyUSM_Fractional_Algorithm4

namespace DoubleGreedyUSM.Fractional

/-- Proof of Theorem A.1, second display (PDF p. 9): for Algorithm 4 run on a nonnegative
submodular `f` in the order `l` of the ground set, with `n = l.length`,
`F(OPT_0) − F(OPT_n) ≤ 1/2 · [F(x_n) − F(x_0)] + 1/2 · [F(y_n) − F(y_0)] ≤ (F(x_n) + F(y_n))/2`. -/
theorem telescoped {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (hf0 : ∀ S : Finset X, 0 ≤ f S)
    (l : List X) (hl : l.Nodup) (hcov : ∀ x, x ∈ l)
    (O : Finset X) (hO : ∀ S : Finset X, f S ≤ f O) :
    NonmonotoneSubmod.Shared.F f (optI O (state f l 0))
        - NonmonotoneSubmod.Shared.F f (optI O (state f l l.length))
      ≤ 1 / 2 * (NonmonotoneSubmod.Shared.F f (state f l l.length).1
            - NonmonotoneSubmod.Shared.F f (state f l 0).1)
        + 1 / 2 * (NonmonotoneSubmod.Shared.F f (state f l l.length).2
            - NonmonotoneSubmod.Shared.F f (state f l 0).2) ∧
    1 / 2 * (NonmonotoneSubmod.Shared.F f (state f l l.length).1
            - NonmonotoneSubmod.Shared.F f (state f l 0).1)
        + 1 / 2 * (NonmonotoneSubmod.Shared.F f (state f l l.length).2
            - NonmonotoneSubmod.Shared.F f (state f l 0).2)
      ≤ (NonmonotoneSubmod.Shared.F f (state f l l.length).1
          + NonmonotoneSubmod.Shared.F f (state f l l.length).2) / 2 := by sorry

end DoubleGreedyUSM.Fractional
