-- Prove2me | Theorems.Thm_BoundedDegreeST_PlusOne_theorem_1_2
-- name    : BoundedDegreeST.PlusOne.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:53:02.689385+00:00
-- url     : https://prove2.me/theorems/8f31cc20-02a7-4b67-b982-f3049d10fb72
-- title:
--   Theorem 1.2 — cost at most optimum, degrees at most B + 1
-- statement:
--   For a finite simple undirected graph $G=(V,E)$, arbitrary real edge costs $c_e$, and integer upper bounds $B_v$, suppose the bounded-degree spanning-tree LP is feasible. The Figure 4 algorithm started with no selected edges and degree constraints at every vertex has a terminating run, every run takes at most $2|V|-1$ iterations, and every returned spanning tree $T$ satisfies
--
--   $$
--   \deg_T(v)\le B_v+1\quad(v\in V),\qquad
--   c(T)\le\sum_{e\in E}c_e x_e\quad\text{for every LP-feasible }x.
--   $$
--
--   In particular, $c(T)\le c(T_0)$ for every spanning tree $T_0$ satisfying all the original degree bounds, hence $c(T)$ is at most the original optimum. This is the paper's $(1,B_v+1)$ approximation guarantee.
--
--   **Formalization Note** The goal uses LP-MBDCT with $F=\varnothing$ and $W=V$, which gives LP (1)–(5). The iteration bound represents the combinatorial part of polynomial time; LP solver complexity is outside the formal statement. Run existence prevents an empty return relation from making the guarantee vacuous.
-- source:
--   Singh, Lau, Approximating minimum bounded degree spanning trees to within one of optimal, STOC 2007, p. 661, Theorem 1.2; p. 662, Eqs. (1)–(5); p. 666, Figure 4

import Definitions.Def_BoundedDegreeST_PlusOne_Algorithm

namespace BoundedDegreeST.PlusOne

/-- Singh–Lau, Theorem 1.2, p. 661, via Figure 4 at `F = ∅`, `W = V`. -/
theorem theorem_1_2 {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (c : Sym2 V → ℝ) (B : V → ℤ)
    (hsimple : SimpleEdges E)
    (hfeasible : ∃ x, Feasible E B Finset.univ ∅ x) :
    (∃ T, Returns c (initial E B) T) ∧
    (∀ k, Chain c (initial E B) k →
      (k : ℤ) ≤ 2 * (Fintype.card V : ℤ) - 1) ∧
    (∀ T, Returns c (initial E B) T →
      T ⊆ E ∧ IsSpanningTree T ∧
      (∀ v : V, (degree T v : ℤ) ≤ B v + 1) ∧
      (∀ x, Feasible E B Finset.univ ∅ x →
        cost c T ≤ ∑ e ∈ E, c e * x e) ∧
      (∀ T₀ : Finset (Sym2 V), T₀ ⊆ E → IsSpanningTree T₀ →
        (∀ v : V, (degree T₀ v : ℤ) ≤ B v) →
        cost c T ≤ cost c T₀)) := by sorry
end BoundedDegreeST.PlusOne
