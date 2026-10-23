-- Prove2me | Theorems.Thm_BicliqueSDP_Chain_lemma_3_3
-- name    : BicliqueSDP.Chain.lemma_3_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:30.09817+00:00
-- url     : https://prove2.me/theorems/48d6f23f-8def-4c08-b852-22a73344aa1b
-- title:
--   Lemma 3.3, p. 13 — h₁(G) = min{λ : λI + Z − C ⪰ 0, Z ∈ S_G}, the minimum attained
-- statement:
--   Let $G=(V=V_1\cup V_2,E)$ be a bipartite graph, $C=\frac12\begin{pmatrix}0&J\\J&0\end{pmatrix}$, and $S_G$ the set of symmetric matrices indexed by $V$ that vanish outside the edges of $G$ (including the diagonal). Then the semidefinite program (33) defining $h_1(G)$ and the program (32) have the same value, and the minimum in (32) is attained:
--
--   $$h_1(G)=\min_{\lambda\in\mathbb R,\,Z\in\mathcal S^{|V|}}\{\lambda:\lambda I+Z-C\succeq0,\ Z\in S_G\}=\max_{X\in\mathcal S^{|V|}}\{\langle C,X\rangle:X\succeq0,\ \mathrm{Tr}(X)=1,\ X_{ij}=0\text{ for }\{i,j\}\in E\}.$$
--
--   This is the strong duality used in §3.3: the dual formulation gives the lower bound $\frac12\sqrt{g(G)}\le h_1(G)$ and a dual optimal solution, which yields relations (40)–(41).
--
--   **Formalization Note** In the paper the left-hand side is the Lasserre bound of order one (30). The mission defines $h_1(G)$ directly by (33) = (9), so the statement is the equality of the values of (32) and (33), together with the existence of a matrix $Z\in S_G$ with $h_1(G)I+Z-C\succeq0$ (the paper writes "min"). The minimum is a real infimum, `sInf`.
-- source:
--   Laurent, Polak, Vargas, Semidefinite approximations for bicliques and biindependent pairs, arXiv:2302.08886v2, p. 13, Lemma 3.3, programs (32) and (33)

import Mathlib
import Definitions.Def_BicliqueSDP_Chain_Model

namespace BicliqueSDP.Chain

/-- Lemma 3.3 (p. 13): the value of the dual program (32) equals `h₁(G)` as defined by (33) = (9),
and the minimum in (32) is attained. -/
theorem lemma_3_3 {V1 V2 : Type} [Fintype V1] [Fintype V2] [DecidableEq V1] [DecidableEq V2]
    (E : V1 → V2 → Prop) :
    h1Dual E = h1 E ∧ ∃ Z, H1DualFeasible E (h1 E) Z := by sorry

end BicliqueSDP.Chain
