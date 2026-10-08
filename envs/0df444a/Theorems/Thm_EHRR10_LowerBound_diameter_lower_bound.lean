-- Prove2me | Theorems.Thm_EHRR10_LowerBound_diameter_lower_bound
-- name    : EHRR10.LowerBound.diameter_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:31:59.559228+00:00
-- url     : https://prove2.me/theorems/d7fdb917-9db2-480b-9026-ca33dc7af4e0
-- title:
--   p. 3, main result — D(n/4, n) = Ω(n²/log n): the base abstraction admits almost-quadratic diameter
-- statement:
--   For a graph $G$ in the base abstraction $\mathcal B_{d,n}$ (a graph on a nonempty family of $d$-element subsets of $[n]$ satisfying condition i); see the definition `EHRR10.LowerBound.BaseAbstraction`), let $\mathrm{dist}_G(u,v)$ be the length of a shortest path from $u$ to $v$, and let $D(d,n)$ be the largest diameter of a graph in $\mathcal B_{d,n}$. The main result of Eisenbrand, Hähnle, Razborov and Rothvoß is
--
--   $$D(n/4,\, n) = \Omega\!\left(\frac{n^2}{\log n}\right).$$
--
--   Explicitly: there are a constant $c > 0$ and a threshold $N$ such that for every $n \ge N$ divisible by $4$ there exist a family $V$ of $(n/4)$-element subsets of $[n]$ and a graph $G \in \mathcal B_{n/4,n}$ on $V$ with two vertices $u, v$ satisfying
--
--   $$\mathrm{dist}_G(u,v) \;\ge\; c\,\frac{n^2}{\log n}.$$
--
--   Since the graph of every non-degenerate $d$-dimensional polyhedron with $n$ facets lies in $\mathcal B_{d,n}$, upper bounds for $D(d,n)$ bound the diameter of polyhedra; this theorem shows that no bound better than almost quadratic in $n$ can be obtained from condition i) alone, so a linear (Hirsch-type) bound needs further geometric properties of polyhedra.
--
--   **Formalization Note** The page writes $D(n/4,n)$ without rounding; it is read literally, for $n$ a multiple of $4$ with dimension exactly $n/4$. $\Omega(\cdot)$ is made explicit as $\exists\, c > 0,\ \exists N,\ \forall n \ge N$. The logarithm is the natural one (`Real.log`); the base only rescales $c$, and $N$ keeps $\log n > 0$ in the range considered. "$D(n/4,n) \ge B$" is stated as the existence of one graph in $\mathcal B_{n/4,n}$ with two vertices at distance at least $B$, which is the same statement without defining $D$ as a supremum. `SimpleGraph.dist` is $0$ for unreachable pairs, which could only make the inequality harder; condition i) makes every pair reachable anyway. Only the lower half of the $\Omega$ statement is claimed; the page does not claim a matching upper bound.
-- source:
--   Eisenbrand, Hähnle, Razborov, Rothvoß, Diameter of Polyhedra: Limits of Abstraction, Dagstuhl Seminar Proceedings 10211 (2010), http://drops.dagstuhl.de/opus/volltexte/2010/2724, p. 3, 'Our main result is a super-linear lower bound on D(d, n), namely D(n/4, n) = Ω(n²/log n)'

import Mathlib
import Definitions.Def_EHRR10_LowerBound_BaseAbstraction

namespace EHRR10.LowerBound

theorem diameter_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 4 ∣ n →
      ∃ (V : Finset (Finset (Fin n))) (G : SimpleGraph V),
        InB (n / 4) n V G ∧
        ∃ u v : V, c * (n : ℝ) ^ 2 / Real.log n ≤ (G.dist u v : ℝ) := by sorry

end EHRR10.LowerBound
