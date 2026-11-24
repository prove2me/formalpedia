-- Prove2me | Theorems.Thm_BicliqueSDP_Chain_Supplement_theorem_2_8
-- name    : BicliqueSDP.Chain.Supplement.theorem_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:18:13.752985+00:00
-- url     : https://prove2.me/theorems/57d9b1dc-5e37-4ce3-aa7e-aa853c5348f0
-- title:
--   Theorem 2.8 — half cliques, balanced maxima of H_G and the reduction
-- statement:
--   Let $G=(V,E)$ be a finite simple graph with $|E|=|V|(|V|-2)/4$, and let $H_G$ be the graph constructed in Definition 2.5, with its prescribed two parts. Then
--
--   $$G\text{ has a clique of size }|V|/2\quad\Longleftrightarrow\quad
--   \alpha(H_G)=\alpha_{\mathrm{bal}}(H_G).$$
--
--   The complexity conclusion is also included:
--
--   $$\mathrm{HALF\text{-}SIZE\text{-}CLIQUE\text{-}EDGE}\ \le_P\ \alpha\text{-}\mathrm{BAL}\text{-}\mathrm{BIP}.$$
--
--   The result supplies the second reduction in the complexity chain. Its independent-set support is the corrected Lemma 2.6; the equivalence and the reduction themselves are unchanged.
--
--   **Formalization Note** The exact rational edge identity forces an even vertex count. The Lean statement makes evenness explicit and writes the identity as $4m=n(n-2)$ in natural numbers, which is equivalent on that domain and includes $n=0$. This prevents the spurious $n=1$ instance caused by truncated natural subtraction.
--
--   Differences from the source:
--   - encoding: The paper states the rational identity m=n(n-2)/4 and polynomial-time reducibility on graph instances → Lean uses Even n and the natural-number identity 4*m=n*(n-2), together with CookPvsNP.PolyReducible on fixed graph codes; reason: The real identity implies evenness, so the two assumptions describe exactly the source domain; a bare natural-number identity would wrongly admit n=1.
-- source:
--   Laurent, Polak, Vargas, Semidefinite approximations for bicliques and biindependent pairs, arXiv:2302.08886v2, p. 10, Theorem 2.8

import Definitions.Def_BicliqueSDP_Chain_Supplement_Problems
set_option autoImplicit false

namespace BicliqueSDP.Chain.Supplement

/-- Theorem 2.8: the full graph equivalence AND the polynomial-time reduction.
Evenness comes from the exact rational edge-count identity in the paper and prevents
natural subtraction from admitting the spurious one-vertex graph. -/
theorem theorem_2_8 :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Even (Fintype.card V) →
      4 * Nat.card G.edgeSet = Fintype.card V * (Fintype.card V - 2) →
      (HasHalfClique G ↔ alpha (HGEdge G) = alphaBal (HGEdge G))) ∧
    CookPvsNP.PolyReducible halfSizeCliqueEdge alphaBalBip := by sorry

end BicliqueSDP.Chain.Supplement
