-- Prove2me | Theorems.Thm_DoubleGreedyUSM_Fractional_lemma_A_2
-- name    : DoubleGreedyUSM.Fractional.lemma_A_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T08:05:35.212868+00:00
-- url     : https://prove2.me/theorems/3250b768-32c5-424c-abe2-eeb5df66ae54
-- title:
--   Lemma A.2 — $F(OPT_{i-1}) - F(OPT_i) \le \frac12[F(x_i) - F(x_{i-1}) + F(y_i) - F(y_{i-1})]$
-- statement:
--   Let $f : 2^{\mathcal N} \to \mathbb R$ be submodular with multilinear extension $F$, let $OPT$ be an optimal solution, and run Algorithm 4 on $f$ in an order $u_1, \dots, u_n$ of the ground set, with states $x_i, y_i$ and $OPT_i = (OPT \vee x_i) \wedge y_i$. Then for every $1 \le i \le n$,
--   $$F(OPT_{i-1}) - F(OPT_i) \le \frac12 \cdot \bigl[F(x_i) - F(x_{i-1}) + F(y_i) - F(y_{i-1})\bigr].$$
--
--   The loss of the reference sequence in one iteration is at most the average gain of the two solutions the algorithm maintains. Summed over $i$ and telescoped, this gives Theorem A.1.
--
--   **Formalization Note.** The statement is deterministic: Algorithm 4 makes no random choice before its output step. Nonnegativity of $f$ is not needed and is not assumed. The order is a duplicate-free list containing every element of the finite type $X$.
-- source:
--   Buchbinder, Feldman, Naor, Schwartz, A Tight Linear Time (1/2)-Approximation for Unconstrained Submodular Maximization, FOCS 2012 version, Lemma A.2 (PDF p. 9)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_DoubleGreedyUSM_Fractional_Algorithm4

namespace DoubleGreedyUSM.Fractional

/-- Lemma A.2 (PDF p. 9): for Algorithm 4 run on a submodular `f` in the order `l` of the ground
set and `OPT_i = (OPT ∨ x_i) ∧ y_i`, for every `1 ≤ i ≤ n`,
`F(OPT_{i−1}) − F(OPT_i) ≤ 1/2 · [F(x_i) − F(x_{i−1}) + F(y_i) − F(y_{i−1})]`. -/
theorem lemma_A_2 {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f)
    (l : List X) (hl : l.Nodup) (hcov : ∀ x, x ∈ l)
    (O : Finset X) (hO : ∀ S : Finset X, f S ≤ f O)
    (i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ l.length) :
    NonmonotoneSubmod.Shared.F f (optI O (state f l (i - 1)))
        - NonmonotoneSubmod.Shared.F f (optI O (state f l i))
      ≤ 1 / 2 * (NonmonotoneSubmod.Shared.F f (state f l i).1
          - NonmonotoneSubmod.Shared.F f (state f l (i - 1)).1
          + NonmonotoneSubmod.Shared.F f (state f l i).2
          - NonmonotoneSubmod.Shared.F f (state f l (i - 1)).2) := by sorry

end DoubleGreedyUSM.Fractional
