-- Prove2me | Theorems.Thm_DoubleGreedyUSM_Deterministic_deterministic_usm_third
-- name    : DoubleGreedyUSM.Deterministic.deterministic_usm_third
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:30:51.361361+00:00
-- url     : https://prove2.me/theorems/eb8e0bd4-a034-452b-b77e-68cc1e95daa8
-- title:
--   Theorem I.1 — Algorithm 1 returns a set of value at least $f(OPT)/3$
-- statement:
--   This is the approximation guarantee of the deterministic double greedy algorithm for unconstrained submodular maximization.
--
--   Let $\mathcal N$ be a finite ground set and $f : 2^{\mathcal N} \to \mathbb R_{\ge 0}$ a nonnegative submodular function, i.e. $f(A) + f(B) \ge f(A \cup B) + f(A \cap B)$ for all $A, B \subseteq \mathcal N$. Let $u_1, \dots, u_n$ be any order of $\mathcal N$, and let $(X_n, Y_n)$ be the final state of Algorithm 1 (DeterministicUSM) run in this order. Then $X_n = Y_n$ and
--   $$\max_{S \subseteq \mathcal N} f(S) \le 3\, f(X_n).$$
--
--   That is, Algorithm 1 is a $(1/3)$-approximation algorithm for maximizing a nonnegative submodular function with no constraint, for every order of the ground set. It evaluates $f$ on four sets per element, so it makes a linear number of value-oracle queries. Theorem II.3 shows the factor $1/3$ is tight for this algorithm.
--
--   **Formalization Note** The paper states the theorem as "there exists a deterministic linear time $(1/3)$-approximation algorithm". The existential is replaced by the guarantee for the paper's Algorithm 1, for every order, because an existential without the running time would be satisfied by exhaustive search; the running time itself is not formalized. The ratio is multiplied out ($OPT \le 3 f(X_n)$) because $OPT$ may be $0$. The first conjunct $X_n = Y_n$ is the paper's "return $X_n$ (or equivalently $Y_n$)". The order is a duplicate-free list `l` containing every element; $f(OPT)$ is the referenced maximum `NonmonotoneSubmod.Shared.OPT f`, and submodularity is the lattice form of the paper's footnote 1.
-- source:
--   Buchbinder, Feldman, Naor, Schwartz, A Tight Linear Time (1/2)-Approximation for Unconstrained Submodular Maximization, FOCS 2012 version, Theorem I.1 (PDF p. 2; proof on PDF p. 3)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_DoubleGreedyUSM_Deterministic_Algorithm1

namespace DoubleGreedyUSM.Deterministic

theorem deterministic_usm_third {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f) (l : List X)
    (hl : l.Nodup) (hcov : ∀ x, x ∈ l) :
    (state f l l.length).1 = (state f l l.length).2 ∧
      NonmonotoneSubmod.Shared.OPT f ≤ 3 * f (state f l l.length).1 := by sorry

end DoubleGreedyUSM.Deterministic
