-- Prove2me | Theorems.Thm_AppliedComb_InclExcl_perm_N_eq
-- name    : AppliedComb.InclExcl.perm_N_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:09:56.207194+00:00
-- url     : https://prove2.me/theorems/50f485fa-a64c-493d-829b-053e0704121b
-- title:
--   Lemma 7.10 — N(S) = (n − k)! for the permutations of [n]
-- statement:
--   Let $n \ge 0$, let $X$ be the set of all permutations $\sigma$ of $[n]$, and say that $\sigma$ satisfies property $P_i$ ($i \in [n]$) if $\sigma(i) = i$. For $S \subseteq [n]$ let $N(S)$ be the number of permutations satisfying $P_i$ for all $i \in S$, i.e. fixing every point of $S$. Then $N(S)$ depends only on $|S|$; in fact, if $|S| = k$ then
--   $$N(S) = (n - k)!.$$
--
--   Together with the Principle of Inclusion-Exclusion (Theorem 7.7) this gives the formula for the number of derangements (Theorem 7.11).
--
--   **Formalization Note.** Permutations are `Equiv.Perm (Fin n)`, the properties are `AppliedComb.InclExcl.FixesPoint n`, and $N$ is `AppliedComb.InclExcl.N`. The two clauses are: equal cardinality gives equal $N$; and $|S| = k$ gives $N(S) = (n-k)!$. Since $k \le n$, the subtraction $n - k$ in $\mathbb N$ is exact. The book fixes $n$ positive; the statement is made for all $n \ge 0$.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 147, Lemma 7.10

import Mathlib
import Definitions.Def_AppliedComb_InclExcl_N
import Definitions.Def_AppliedComb_InclExcl_properties

namespace AppliedComb.InclExcl

/-- Lemma 7.10, Keller & Trotter p. 147: with `X` the permutations of `[n]` and `P_i` the
property "`σ(i) = i`", `N(S)` depends only on `|S|`, and `N(S) = (n - k)!` when `|S| = k`. -/
theorem perm_N_eq (n : ℕ) :
    (∀ S T : Finset (Fin n), S.card = T.card →
      N (FixesPoint n) S = N (FixesPoint n) T) ∧
    ∀ (k : ℕ) (S : Finset (Fin n)), S.card = k →
      N (FixesPoint n) S = (n - k).factorial := by sorry

end AppliedComb.InclExcl
