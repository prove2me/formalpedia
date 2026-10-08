-- Prove2me | Theorems.Thm_DoubleGreedyUSM_Deterministic_tight_example
-- name    : DoubleGreedyUSM.Deterministic.tight_example
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:30:47.321728+00:00
-- url     : https://prove2.me/theorems/4e406e5a-e7f6-4d18-b1d2-db43b0b815f9
-- title:
--   Theorem II.3 — the factor $1/3$ is tight for Algorithm 1
-- statement:
--   For every $\varepsilon > 0$ there is a finite ground set $\mathcal N$, a nonnegative submodular function $f : 2^{\mathcal N} \to \mathbb R_{\ge 0}$ with $\max_{S \subseteq \mathcal N} f(S) > 0$, and an order $u_1, \dots, u_n$ of $\mathcal N$, such that the output $X_n$ of Algorithm 1 run in this order satisfies
--   $$f(X_n) \le \left(\tfrac13 + \varepsilon\right) \max_{S \subseteq \mathcal N} f(S).$$
--
--   The analysis of Theorem I.1 therefore cannot be improved for Algorithm 1: its approximation ratio is exactly $1/3$. In the paper the instance is the cut function of a weighted directed graph on five vertices.
--
--   **Formalization Note** The ground set is `Fin n` for some $n$, and the order is a duplicate-free list covering it. The requirement $\max f > 0$ is part of the statement because without it the zero function would satisfy the inequality for every algorithm. Nonnegativity and submodularity of $f$ are required of the witness, since the paper's problem is maximization of a nonnegative submodular function. The paper's instance is not fixed in the statement; any instance proves it.
-- source:
--   Buchbinder, Feldman, Naor, Schwartz, A Tight Linear Time (1/2)-Approximation for Unconstrained Submodular Maximization, FOCS 2012 version, §II.A, Theorem II.3 and Figure 1 (PDF p. 4)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_DoubleGreedyUSM_Deterministic_Algorithm1

namespace DoubleGreedyUSM.Deterministic

theorem tight_example :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∃ f : Finset (Fin n) → ℝ, ∃ l : List (Fin n),
      l.Nodup ∧ (∀ x, x ∈ l) ∧ (∀ S, 0 ≤ f S) ∧ NonmonotoneSubmod.Shared.Submodular f ∧
        0 < NonmonotoneSubmod.Shared.OPT f ∧
        f (state f l l.length).1 ≤ (1 / 3 + ε) * NonmonotoneSubmod.Shared.OPT f := by sorry

end DoubleGreedyUSM.Deterministic
