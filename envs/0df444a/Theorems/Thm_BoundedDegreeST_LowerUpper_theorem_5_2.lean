-- Prove2me | Theorems.Thm_BoundedDegreeST_LowerUpper_theorem_5_2
-- name    : BoundedDegreeST.LowerUpper.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:23:34.266746+00:00
-- url     : https://prove2.me/theorems/1fac2a1d-8f79-4a32-9f49-e2baa9bf2841
-- title:
--   Theorem 5.2 — MBDCT Algorithm2 is a (1, A_v − 1, B_v + 1)-approximation for the minimum bounded degree connecting tree problem
-- statement:
--   Let $G=(V,E)$ be a finite simple graph with edge costs $c_e\in\mathbb R$ of any sign, $F$ a forest on $V$ with $E(F)\cap E(G)=\varnothing$, and let $A_v$ ($v\in U$) and $B_v$ ($v\in W$) be integer lower and upper degree bounds. An **$F$-tree** is a set $H\subseteq E$ such that $H\cup F$ is a spanning tree, and $d_H(v)$ is the number of edges of $H$ at $v$. Assume LP-MBDCT$(G,\mathcal A,\mathcal B,U,W,F)$ is feasible. Then MBDCT Algorithm2 (Figure 5) satisfies:
--
--   1. **(a run exists)** some run returns a set $H$;
--   2. **(iteration bound)** every run makes at most $|V|-|F|-1+|U\cup W|$ iterations;
--   3. **(guarantee)** every returned $H$ is an $F$-tree in $G$ with
--
--   $$
--   c(H)\ \le\ \sum_{e\in E}c_e x_e\ \text{ for every feasible }x,\qquad A_v-1\le d_H(v)\ (v\in U),\qquad d_H(v)\le B_v+1\ (v\in W).
--   $$
--
--   At $F=\varnothing$ this returns a spanning tree of cost at most OPT with $A_v-1\le d_T(v)\le B_v+1$, the paper's abstract claim for the problem with both lower and upper bounds.
--
--   **Formalization Note** "There is a polynomial time $(1,A_v-1,B_v+1)$-approximation algorithm" is made explicit as (1)–(3) for the algorithm of Figure 5 quantified over every choice it leaves open; "polynomial time" is the iteration bound, with the LP solved by an oracle (any basic optimal solution), and the ellipsoid/separation running time is not modelled. "Cost at most the LP optimum" is $c(H)\le c\cdot x$ for every feasible $x$. LP feasibility is an explicit hypothesis. Step 4 carries the guard "no 1-edge" stated in the paper's text under Lemma 5.1 (see the Algorithm definition).
-- source:
--   Singh, Lau, Approximating minimum bounded degree spanning trees to within one of optimal, STOC 2007, p. 668, Theorem 5.2 and Figure 5; p. 665, the MBDCT problem and F-trees; p. 667, §5

import Definitions.Def_BoundedDegreeST_LowerUpper_Algorithm

namespace BoundedDegreeST.LowerUpper

/-- Singh–Lau, Theorem 5.2, p. 668: MBDCT Algorithm2 is a
`(1, A_v − 1, B_v + 1)`-approximation for the minimum bounded degree connecting
tree problem. On a well-formed instance whose LP is feasible:
(1) some run returns; (2) every run makes at most `|V| − |F| − 1 + |U ∪ W|`
iterations (the LP is solved by an oracle); (3) every returned `H` is an
`F`-tree in `E` with `c(H)` at most the BoundedDegreeST.PlusOne.cost of every feasible LP solution
and `A_v − 1 ≤ d_H(v)` on `U`, `d_H(v) ≤ B_v + 1` on `W`. -/
theorem theorem_5_2 {V : Type*} [Fintype V] [DecidableEq V]
    (c : Sym2 V → ℝ) (I : Instance V)
    (hvalid : Valid I) (hfeasible : ∃ x, Feasible I.E I.A I.B I.U I.W I.F x) :
    (∃ H, Returns c I H) ∧
    (∀ k, Chain c I k →
      (k : ℤ) ≤ (Fintype.card V : ℤ) - (I.F.card : ℤ) - 1 + ((I.U ∪ I.W).card : ℤ)) ∧
    (∀ H, Returns c I H →
      H ⊆ I.E ∧ BoundedDegreeST.PlusOne.IsSpanningTree (H ∪ I.F) ∧
      (∀ x, Feasible I.E I.A I.B I.U I.W I.F x →
        BoundedDegreeST.PlusOne.cost c H ≤ ∑ e ∈ I.E, c e * x e) ∧
      (∀ v ∈ I.U, I.A v - 1 ≤ (degree H v : ℤ)) ∧
      (∀ v ∈ I.W, (degree H v : ℤ) ≤ I.B v + 1)) := by sorry

end BoundedDegreeST.LowerUpper
