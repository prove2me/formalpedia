-- Prove2me | Theorems.Thm_AppliedComb_InclExcl_surj_N_eq
-- name    : AppliedComb.InclExcl.surj_N_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:09:32.125468+00:00
-- url     : https://prove2.me/theorems/30819acb-6340-4023-b7e5-9e88db8fa29a
-- title:
--   Lemma 7.8 — N(S) = (m − k)^n for the functions [n] → [m]
-- statement:
--   Let $n, m \ge 0$, let $X$ be the set of all functions $f : [n] \to [m]$, and say that $f$ satisfies property $P_i$ ($i \in [m]$) if $i$ is not in the range of $f$. For $S \subseteq [m]$ let $N(S)$ be the number of $f \in X$ satisfying $P_i$ for all $i \in S$. Then $N(S)$ depends only on $|S|$; in fact, if $|S| = k$ then
--   $$N(S) = (m - k)^n.$$
--
--   Together with the Principle of Inclusion-Exclusion (Theorem 7.7) this gives the formula for the number of surjections (Theorem 7.9).
--
--   **Formalization Note.** Functions are `Fin n → Fin m`, the properties are `AppliedComb.InclExcl.NotInRange n m`, and $N$ is `AppliedComb.InclExcl.N`. The two clauses are: equal cardinality of $S$ and $T$ gives $N(S) = N(T)$; and $|S| = k$ gives $N(S) = (m-k)^n$. Since $k = |S| \le m$, the natural-number subtraction $m - k$ is exact. The book takes $n, m$ positive; the statement is made for all $n, m \ge 0$ (with $0^0 = 1$), where it is still true.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 146, Lemma 7.8

import Mathlib
import Definitions.Def_AppliedComb_InclExcl_N
import Definitions.Def_AppliedComb_InclExcl_properties

namespace AppliedComb.InclExcl

/-- Lemma 7.8, Keller & Trotter p. 146: with `X` the functions from `[n]` to `[m]` and `P_i`
the property "`i` is not in the range", `N(S)` depends only on `|S|`, and `N(S) = (m - k)^n`
when `|S| = k`. -/
theorem surj_N_eq (n m : ℕ) :
    (∀ S T : Finset (Fin m), S.card = T.card →
      N (NotInRange n m) S = N (NotInRange n m) T) ∧
    ∀ (k : ℕ) (S : Finset (Fin m)), S.card = k → N (NotInRange n m) S = (m - k) ^ n := by sorry

end AppliedComb.InclExcl
