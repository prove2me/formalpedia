-- Prove2me | Theorems.Thm_AssortSearch_MNLQC_theorem_4
-- name    : AssortSearch.MNLQC.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:31:57.766258+00:00
-- url     : https://prove2.me/theorems/5e157dd9-a8da-49bb-b3d8-6b0c998af4de
-- title:
--   Theorem 4: $h^m(v_j) = \pi_j^m(v_j) - L^m(v_j)$ is quasi-convex in $v_j$ on $[0,\infty)$
-- statement:
--   Consider the traditional multinomial logit (MNL) model of consumer choice, without search. There are $n$ variants with preferences $v_1,\dots,v_n > 0$ and a no-purchase option with preference $v_0 > 0$. Variant $i$ has margin $m_i \in \mathbb R$. Including a variant with demand $q$ costs $c(q)$, where the operational cost $c$ is concave and increasing on $[0,1]$. With assortment $S$, variant $i$'s demand is $q_i^m(S) = v_i/(\sum_{k\in S} v_k + v_0)$ and its profit is $\pi_i(S) = m_i q_i(S) - c(q_i(S))$.
--
--   Fix an assortment $S$ and a variant $j \notin S$, and regard $j$'s preference $v_j$ as a variable. Let $\pi_i(v_j)$ be variant $i$'s profit in the assortment $S \cup \{j\}$, and let $L(v_j) = \sum_{i\in S}\pi_i(S) - \sum_{i\in S}\pi_i(v_j)$ be the profit lost on the variants already in $S$. Then the profit change from adding $j$,
--
--   $$h^m(v_j) = \pi_j^m(v_j) - L^m(v_j),$$
--
--   is quasi-convex in $v_j$ on $[0,\infty)$. That is, for every $r \in \mathbb R$ the set $\{v_j \ge 0 : h^m(v_j) \le r\}$ is an interval.
--
--   Because $h^m$ is quasi-convex, it attains its maximum over any interval $[0, \bar v]$ at an endpoint. If adding a less popular variant is profitable, adding a more popular one is even better. This is how the paper shows that the optimal no-search assortment consists of the most popular variants. It extends van Ryzin and Mahajan's (1999) result from their newsvendor cost to any concave increasing cost.
--
--   **Formalization Note** Variants are `Fin n`, 0-based, and the no-purchase preference $v_0$ is a separate positive real. $j \notin S$ is assumed, as the paper's "adding variant $j$ to an assortment $S$" requires. $c$ is assumed concave and increasing only on $[0,1]$, where demands lie, and nothing is assumed about $c(0)$, so $h^m(0) = -c(0)$ need not be $0$. No differentiability of $c$ is assumed. Margins may differ across variants, as in the paper's model. The paper's proof writes a common margin, but the theorem does not need one.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 13 (PDF 15), Theorem 4

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model
import Definitions.Def_AssortSearch_MNLQC_Model

namespace AssortSearch.MNLQC

/-- **Theorem 4** (p. 13): in the no-search MNL model, with a concave increasing operational
cost `c` on `[0, 1]` and arbitrary margins `m_i`, the function
`h^m(v_j) = π_j^m(v_j) − L^m(v_j)` is quasi-convex in the added variant's preference `v_j`
on `[0, ∞)`. -/
theorem theorem_4
    {n : ℕ} (m : Fin n → ℝ) (c : ℝ → ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (S : Finset (Fin n)) (j : Fin n)
    (hv : ∀ i, 0 < v i) (hv0 : 0 < v0)
    (hc_concave : ConcaveOn ℝ (Set.Icc 0 1) c) (hc_mono : MonotoneOn c (Set.Icc 0 1))
    (hj : j ∉ S) :
    QuasiconvexOn ℝ (Set.Ici 0) (hm m c v v0 S j) := by sorry

end AssortSearch.MNLQC
