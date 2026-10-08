-- Prove2me | Theorems.Thm_DoubleGreedyUSM_Deterministic_lemma_II_1
-- name    : DoubleGreedyUSM.Deterministic.lemma_II_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:30:08.478687+00:00
-- url     : https://prove2.me/theorems/75e7f649-ca63-4310-b6a1-d5154b947f74
-- title:
--   Lemma II.1 — $a_i + b_i \ge 0$ along the run of Algorithm 1
-- statement:
--   Let $\mathcal N$ be a finite ground set, $f : 2^{\mathcal N} \to \mathbb R$ a submodular function, i.e. $f(A) + f(B) \ge f(A \cup B) + f(A \cap B)$ for all $A, B \subseteq \mathcal N$, and $u_1, \dots, u_n$ an enumeration of $\mathcal N$ (each element exactly once). Run Algorithm 1 (DeterministicUSM) in this order, producing the states $(X_i, Y_i)$, and let
--   $$a_i = f(X_{i-1} \cup \{u_i\}) - f(X_{i-1}), \qquad b_i = f(Y_{i-1} \setminus \{u_i\}) - f(Y_{i-1})$$
--   be the two marginal gains the algorithm compares in iteration $i$. Then for every $1 \le i \le n$,
--   $$a_i + b_i \ge 0.$$
--
--   In words, in every iteration at least one of the two options (adding $u_i$ to $X$, removing $u_i$ from $Y$) does not decrease the value of its solution. The lemma is used in the proof of Lemma II.2.
--
--   **Formalization Note** The element $u_i$ is `l[i - 1]` and the state before iteration $i$ is `state f l (i - 1)`. Nonnegativity of $f$ is not needed and is not assumed. The paper's submodularity sentence in the introduction ("for every $A \subseteq B \subseteq \mathcal N$ and $u \in \mathcal N$") is a slip, since for $u \in B \setminus A$ it would force monotonicity; the formalization uses the equivalent lattice form of the paper's footnote 1, via the referenced definition `NonmonotoneSubmod.Shared.Submodular`.
-- source:
--   Buchbinder, Feldman, Naor, Schwartz, A Tight Linear Time (1/2)-Approximation for Unconstrained Submodular Maximization, FOCS 2012 version, Lemma II.1 (PDF p. 3)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_DoubleGreedyUSM_Deterministic_Algorithm1

namespace DoubleGreedyUSM.Deterministic

theorem lemma_II_1 {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (l : List X) (hl : l.Nodup)
    (hcov : ∀ x, x ∈ l) :
    ∀ i (h1 : 1 ≤ i) (h2 : i ≤ l.length),
      addGain f (state f l (i - 1)) (l[i - 1]'(by omega)) +
        removeGain f (state f l (i - 1)) (l[i - 1]'(by omega)) ≥ 0 := by sorry

end DoubleGreedyUSM.Deterministic
