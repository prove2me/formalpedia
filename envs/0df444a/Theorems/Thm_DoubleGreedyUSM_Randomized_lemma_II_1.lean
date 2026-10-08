-- Prove2me | Theorems.Thm_DoubleGreedyUSM_Randomized_lemma_II_1
-- name    : DoubleGreedyUSM.Randomized.lemma_II_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:10:00.821307+00:00
-- url     : https://prove2.me/theorems/1d3977aa-1a50-468f-a2e9-30556ba65e5b
-- title:
--   Lemma II.1 — nonnegative sum of the two marginal gains
-- statement:
--   Let $f:2^{\mathcal N}\to\mathbb R$ be submodular, and run Algorithm 2 in any order $u_1,\ldots,u_n$ of the finite ground set. At every step $1\le i\le n$ and every state $(X_{i-1},Y_{i-1})$ having nonzero probability, let $a_i$ be the gain from adding $u_i$ to $X_{i-1}$ and $b_i$ the gain from removing it from $Y_{i-1}$. Then
--
--   $$a_i+b_i\ge 0.$$
--
--   This inequality rules out simultaneous negative gains and supports the case split in Lemma III.1.
--
--   **Formalization Note** Lemma II.1 is printed for Algorithm 1 and applied to Algorithm 2 in §III. The statement is evaluated at every reachable Algorithm 2 state. Nonnegativity of $f$ is unnecessary for this local inequality. The proof text's $Y_i$ in one set identity is a printing slip; the intended set is $Y_{i-1}$.
-- source:
--   Buchbinder, Feldman, Naor, Schwartz, A Tight Linear Time (1/2)-Approximation for Unconstrained Submodular Maximization, FOCS 2012 version, Lemma II.1 (PDF p. 3), applied in proof of Lemma III.1 (PDF p. 5)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_DoubleGreedyUSM_Randomized_Algorithm2

namespace DoubleGreedyUSM.Randomized

/-- Lemma II.1 (PDF p. 3), applied to each reachable state of Algorithm 2. -/
theorem lemma_II_1 {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (l : List X) (hl : l.Nodup) (hcov : ∀ x : X, x ∈ l) :
    ∀ i (hi : 1 ≤ i) (hin : i ≤ l.length) (s : Finset X × Finset X),
      state f l (i - 1) s ≠ 0 →
      0 ≤ (f (insert (l[i - 1]'(by omega)) s.1) - f s.1) +
        (f (s.2.erase (l[i - 1]'(by omega))) - f s.2) := by sorry

end DoubleGreedyUSM.Randomized
