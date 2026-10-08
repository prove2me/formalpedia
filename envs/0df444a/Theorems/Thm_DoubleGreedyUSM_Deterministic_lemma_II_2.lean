-- Prove2me | Theorems.Thm_DoubleGreedyUSM_Deterministic_lemma_II_2
-- name    : DoubleGreedyUSM.Deterministic.lemma_II_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:30:34.691833+00:00
-- url     : https://prove2.me/theorems/a21bbe65-da23-4f8e-983f-80a1ec5d30d3
-- title:
--   Lemma II.2 — the loss $f(OPT_{i-1}) - f(OPT_i)$ is at most the total gain of $X$ and $Y$
-- statement:
--   Let $\mathcal N$ be a finite ground set, $f : 2^{\mathcal N} \to \mathbb R$ a submodular function, $OPT$ an optimal solution, and $u_1, \dots, u_n$ an enumeration of $\mathcal N$. Run Algorithm 1 in this order, producing the states $(X_i, Y_i)$, and let $OPT_i = (OPT \cup X_i) \cap Y_i$. Then for every $1 \le i \le n$,
--   $$f(OPT_{i-1}) - f(OPT_i) \le [f(X_i) - f(X_{i-1})] + [f(Y_i) - f(Y_{i-1})].$$
--
--   The loss of value in one step of the sequence $OPT_0, \dots, OPT_n$ is thus bounded by the total increase in value of the two solutions maintained by the algorithm. Summing over $i$ gives Theorem I.1.
--
--   **Formalization Note** The states are `state f l (i - 1)` and `state f l i`. Nonnegativity of $f$ is not needed and is not assumed. Submodularity is the lattice form of the paper's footnote 1 (referenced definition `NonmonotoneSubmod.Shared.Submodular`).
-- source:
--   Buchbinder, Feldman, Naor, Schwartz, A Tight Linear Time (1/2)-Approximation for Unconstrained Submodular Maximization, FOCS 2012 version, Lemma II.2 (PDF p. 3; proof on PDF p. 4)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_DoubleGreedyUSM_Deterministic_Algorithm1

namespace DoubleGreedyUSM.Deterministic

theorem lemma_II_2 {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (O : Finset X) (hO : ∀ S, f S ≤ f O)
    (l : List X) (hl : l.Nodup) (hcov : ∀ x, x ∈ l) :
    ∀ i, 1 ≤ i → i ≤ l.length →
      f (optI O (state f l (i - 1))) - f (optI O (state f l i)) ≤
        (f (state f l i).1 - f (state f l (i - 1)).1) +
          (f (state f l i).2 - f (state f l (i - 1)).2) := by sorry

end DoubleGreedyUSM.Deterministic
