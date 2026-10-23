-- Prove2me | Theorems.Thm_BicliqueSDP_Chain_proposition_1_2
-- name    : BicliqueSDP.Chain.proposition_1_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:56.330167+00:00
-- url     : https://prove2.me/theorems/bb334f0a-5e69-4f02-ab88-7eeed49861d9
-- title:
--   Proposition 1.2, p. 5 — for every bipartite graph, h(G) ≤ ½√g(G) ≤ h₁(G) ≤ ½√g₁(G) ≤ ¼α(G)
-- statement:
--   Let $G=(V_1\cup V_2,E)$ be a bipartite graph. Write $\alpha(G)$, $g(G)$ and $h(G)$ for the maxima of $|A|+|B|$, $|A|\cdot|B|$ and $\frac{|A|\cdot|B|}{|A|+|B|}$ over the bipartite biindependent pairs $(A,B)$ of $G$, and let $C=\frac12\begin{pmatrix}0&J\\J&0\end{pmatrix}$. The first-order semidefinite bounds are
--   $$g_1(G)=\max\Bigl\{\langle C,X\rangle:\begin{pmatrix}1&\mathrm{diag}(X)^{\mathsf T}\\ \mathrm{diag}(X)&X\end{pmatrix}\succeq0,\ X_{ij}=0\text{ if }\{i,j\}\in E\Bigr\},$$
--   $$h_1(G)=\max\{\langle C,X\rangle:X\succeq0,\ \mathrm{Tr}(X)=1,\ X_{ij}=0\text{ if }\{i,j\}\in E\}.$$
--   Then
--   $$h(G)\le\tfrac12\sqrt{g(G)}\le h_1(G)\le\tfrac12\sqrt{g_1(G)}\le\tfrac14\alpha(G).$$
--
--   The chain shows that the semidefinite bound $h_1$ for the maximum ratio $h$ also bounds $\frac12\sqrt g$, the quantity governing the maximum product, and that it is never weaker than the bound $\frac12\sqrt{g_1}$ obtained from the semidefinite relaxation of $g$ itself; all of them improve on the trivial bound $\frac14\alpha$.
--
--   **Formalization Note** No hypothesis beyond finiteness of $V_1$, $V_2$ and decidability of the edge relation is assumed; either side may be empty.
-- source:
--   Laurent, Polak, Vargas, Semidefinite approximations for bicliques and biindependent pairs, arXiv:2302.08886v2, p. 5, Proposition 1.2 (proof in §3.3, pp. 15–18)

import Mathlib
import Definitions.Def_BicliqueSDP_Chain_Model

namespace BicliqueSDP.Chain

/-- Proposition 1.2 (p. 5): for every bipartite graph `G`,
`h(G) ≤ ½√g(G) ≤ h₁(G) ≤ ½√g₁(G) ≤ ¼α(G)`. -/
theorem proposition_1_2 {V1 V2 : Type} [Fintype V1] [Fintype V2] [DecidableEq V1] [DecidableEq V2]
    (E : V1 → V2 → Prop) [∀ i j, Decidable (E i j)] :
    h E ≤ (1 / 2) * Real.sqrt (g E) ∧ (1 / 2) * Real.sqrt (g E) ≤ h1 E ∧
      h1 E ≤ (1 / 2) * Real.sqrt (g1 E) ∧ (1 / 2) * Real.sqrt (g1 E) ≤ (1 / 4) * alpha E := by sorry

end BicliqueSDP.Chain
