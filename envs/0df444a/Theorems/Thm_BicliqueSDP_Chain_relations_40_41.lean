-- Prove2me | Theorems.Thm_BicliqueSDP_Chain_relations_40_41
-- name    : BicliqueSDP.Chain.relations_40_41
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:36.512346+00:00
-- url     : https://prove2.me/theorems/fd0fb6da-007c-4818-b01f-7ae78d35b0e5
-- title:
--   Relations (40)–(41), p. 16 — at an optimal X of (33), Σ_{j∈V₂} X_ij = 2h₁(G)X_ii (i ∈ V₁) and symmetrically
-- statement:
--   Let $G=(V_1\cup V_2,E)$ be a bipartite graph and let $X$ be an optimal solution of the program (33) defining $h_1(G)$: $X\succeq0$, $\mathrm{Tr}(X)=1$, $X_{ij}=0$ for $\{i,j\}\in E$, and $\langle C,X\rangle=h_1(G)$. Write $h=h_1(G)$. Then
--
--   $$\sum_{j\in V_2}X_{ij}=2h\,X_{ii}\quad(i\in V_1),\qquad \sum_{i\in V_1}X_{ji}=2h\,X_{jj}\quad(j\in V_2).$$
--
--   In the paper's Gram notation $X=(y_i^{\mathsf T}y_j)$, $y'=\sum_{i\in V_1}y_i$, $y''=\sum_{i\in V_2}y_i$, these read $y_i^{\mathsf T}y''=2h\|y_i\|^2$ for $i\in V_1$ (40) and $y_j^{\mathsf T}y'=2h\|y_j\|^2$ for $j\in V_2$ (41). They are the first step of the proof of $h_1(G)\le\frac12\sqrt{g_1(G)}$.
--
--   **Formalization Note** The relations are stated for the matrix $X$ rather than for a Gram factorisation: $y_i^{\mathsf T}y''=\sum_{j\in V_2}X_{ij}$ and $\|y_i\|^2=X_{ii}$. Optimality of $X$ is the paper's hypothesis ("Let X be an optimal solution for the formulation (33)").
-- source:
--   Laurent, Polak, Vargas, Semidefinite approximations for bicliques and biindependent pairs, arXiv:2302.08886v2, p. 16, relations (40) and (41) in the proof of h₁(G) ≤ ½√g₁(G)

import Mathlib
import Definitions.Def_BicliqueSDP_Chain_Model

namespace BicliqueSDP.Chain

/-- Relations (40)–(41) (p. 16), in matrix form: an optimal solution `X` of (33) satisfies
`∑_{j ∈ V₂} X_ij = 2 h₁(G) X_ii` for `i ∈ V₁` and `∑_{i ∈ V₁} X_ji = 2 h₁(G) X_jj` for `j ∈ V₂`. -/
theorem relations_40_41 {V1 V2 : Type} [Fintype V1] [Fintype V2] [DecidableEq V1] [DecidableEq V2]
    (E : V1 → V2 → Prop) (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) (hX : H1Feasible E X)
    (hopt : frob Cmat X = h1 E) :
    (∀ i : V1, ∑ j : V2, X (Sum.inl i) (Sum.inr j) = 2 * h1 E * X (Sum.inl i) (Sum.inl i)) ∧
    (∀ j : V2, ∑ i : V1, X (Sum.inr j) (Sum.inl i) = 2 * h1 E * X (Sum.inr j) (Sum.inr j)) := by sorry

end BicliqueSDP.Chain
