-- Prove2me | Theorems.Thm_DoubleGreedyUSM_Deterministic_opt_endpoints
-- name    : DoubleGreedyUSM.Deterministic.opt_endpoints
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:30:20.579996+00:00
-- url     : https://prove2.me/theorems/0d935602-3da9-4110-907d-0e91ce83a30d
-- title:
--   §II — $OPT_i$ agrees with $X_i, Y_i$ on $u_1..u_i$ and with $OPT$ after; $OPT_0 = OPT$, $OPT_n = X_n = Y_n$
-- statement:
--   Let $\mathcal N$ be a finite ground set, $f : 2^{\mathcal N} \to \mathbb R$ a set function, $OPT \subseteq \mathcal N$ an optimal solution (a set maximizing $f$), and $u_1, \dots, u_n$ an enumeration of $\mathcal N$. Run Algorithm 1 in this order, producing the states $(X_i, Y_i)$, and define
--   $$OPT_i = (OPT \cup X_i) \cap Y_i, \qquad 0 \le i \le n.$$
--   Then:
--
--   1. for every $0 \le i \le n$, the set $OPT_i$ coincides with $X_i$ and with $Y_i$ on the elements $u_1, \dots, u_i$, and coincides with $OPT$ on the elements $u_{i+1}, \dots, u_n$;
--   2. $OPT_0 = OPT$;
--   3. the output of the algorithm is $OPT_n = X_n = Y_n$.
--
--   The sequence $OPT_0, \dots, OPT_n$ thus starts at the optimum and ends at the algorithm's output; the proof of Theorem I.1 bounds the loss of value along it.
--
--   **Formalization Note** "Coincides on $u_j$" is stated as: $u_j \in OPT_i$ if and only if $u_j \in X_i$ (respectively $Y_i$, respectively $OPT$), for $u_j$ = `l[j]` with 0-based index `j`. Optimality of $OPT$ is kept as a hypothesis because the page introduces $OPT$ as an optimal solution, although the statement holds for every set. No property of $f$ is needed.
-- source:
--   Buchbinder, Feldman, Naor, Schwartz, A Tight Linear Time (1/2)-Approximation for Unconstrained Submodular Maximization, FOCS 2012 version, §II, paragraph after Lemma II.1 (PDF p. 3)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_DoubleGreedyUSM_Deterministic_Algorithm1

namespace DoubleGreedyUSM.Deterministic

theorem opt_endpoints {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (O : Finset X) (hO : ∀ S, f S ≤ f O) (l : List X) (hl : l.Nodup) (hcov : ∀ x, x ∈ l) :
    (∀ i (hi : i ≤ l.length),
      (∀ j (hj : j < i),
        (l[j]'(by omega) ∈ optI O (state f l i) ↔ l[j]'(by omega) ∈ (state f l i).1) ∧
        (l[j]'(by omega) ∈ optI O (state f l i) ↔ l[j]'(by omega) ∈ (state f l i).2)) ∧
      (∀ j (hj : j < l.length), i ≤ j →
        (l[j] ∈ optI O (state f l i) ↔ l[j] ∈ O))) ∧
    optI O (state f l 0) = O ∧
    optI O (state f l l.length) = (state f l l.length).1 ∧
    (state f l l.length).1 = (state f l l.length).2 := by sorry

end DoubleGreedyUSM.Deterministic
