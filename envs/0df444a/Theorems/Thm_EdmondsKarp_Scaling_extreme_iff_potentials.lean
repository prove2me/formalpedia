-- Prove2me | Theorems.Thm_EdmondsKarp_Scaling_extreme_iff_potentials
-- name    : EdmondsKarp.Scaling.extreme_iff_potentials
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:24:50.832766+00:00
-- url     : https://prove2.me/theorems/3781a361-53c8-4671-8e1c-d465a454ef96
-- title:
--   Theorem 8 — optimality conditions (5a)–(5f) for the Hitchcock problem
-- statement:
--   Consider the Hitchcock network of Figure 1 with $m, n \ge 1$, positive capacities $a_i > 0$, $b_j > 0$ satisfying $\sum_i a_i = \sum_j b_j$, and nonnegative costs $d_{ij} \ge 0$. Let $f$ be a maximum flow. Then $f$ is extreme (of minimum cost among the maximum flows) if and only if there exist real numbers $u_0, u_1, \dots, u_m$ and $v_0, v_1, \dots, v_n$ such that, for all $i = 1,\dots,m$ and $j = 1,\dots,n$,
--   $$\begin{aligned}
--   &u_i - v_j + d_{ij} \ge 0, && (5a)\\
--   &u_i - v_j + d_{ij} > 0 \Rightarrow f_{ij} = 0, && (5b)\\
--   &u_0 > u_i \Rightarrow f_{0i} = 0, && (5c)\\
--   &u_0 < u_i \Rightarrow f_{0i} = a_i, && (5d)\\
--   &v_j > v_0 \Rightarrow f_{j0} = 0, && (5e)\\
--   &v_j < v_0 \Rightarrow f_{j0} = b_j. && (5f)
--   \end{aligned}$$
--
--   This is the specialization to the transportation network of the characterization of minimum-cost flows by labeling functions ($u_i = \pi(s_i)$, $v_j = \pi(t_j)$, $u_0 = \pi(s)$, $v_0 = \pi(t)$). It is the certificate of optimality that the scaling method maintains.
--
--   **Formalization Note** The page prints the second family as "$v_0, v_1, \dots, v_m$"; the conditions index $v$ by $j = 0, \dots, n$, which is what is stated. "Extreme among maximum flows" is formalized with $f$ assumed to be a maximum flow: without that assumption the "if" direction would fail, since the zero flow satisfies (5a)–(5f) for suitable potentials. For a maximum flow, extreme (minimum cost among flows of the same value) is the same as minimum cost among maximum flows. The potentials are real numbers.
-- source:
--   Edmonds, Karp, Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), 1972, p. 259, Theorem 8, (5a)–(5f)

import Mathlib
import Definitions.Def_EdmondsKarp_Scaling_Transport

namespace EdmondsKarp.Scaling

/-- Theorem 8 (p. 259). For the Hitchcock network of Figure 1 with positive capacities `a_i`, `b_j`,
`∑ a_i = ∑ b_j` and nonnegative costs `d_ij`, a maximum flow `f` is extreme (of minimum cost among
the maximum flows) if and only if there exist real `u_0, u_1, …, u_m` and `v_0, v_1, …, v_n` with
(5a)–(5f). The page prints `v_0, …, v_m`; the index of `v` runs over `0, …, n` as (5a)–(5f) show.
"Extreme among maximum flows" is read with `f` ranging over maximum flows (hypothesis `hx`): the zero
flow satisfies (5a)–(5f) for suitable potentials but is not maximum. -/
theorem extreme_iff_potentials {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (T : Transport m n)
    (ha : ∀ i, 0 < T.a i) (hb : ∀ j, 0 < T.b j) (hsum : ∑ i, T.a i = ∑ j, T.b j)
    (hd : ∀ i j, 0 ≤ T.d i j) (x : Flow m n) (hx : IsMaxFlow T x) :
    IsExtreme T x ↔
      ∃ (u0 : ℝ) (u : Fin m → ℝ) (v0 : ℝ) (v : Fin n → ℝ),
        (∀ i j, 0 ≤ u i - v j + T.d i j) ∧
        (∀ i j, 0 < u i - v j + T.d i j → x.fx i j = 0) ∧
        (∀ i, u0 > u i → x.f0 i = 0) ∧
        (∀ i, u0 < u i → x.f0 i = T.a i) ∧
        (∀ j, v j > v0 → x.fz j = 0) ∧
        (∀ j, v j < v0 → x.fz j = T.b j) := by sorry

end EdmondsKarp.Scaling
