-- Prove2me | Theorems.Thm_ConstATSP_Gap_lemma_9_3
-- name    : ConstATSP.Gap.lemma_9_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:47:47.170399+00:00
-- url     : https://prove2.me/theorems/32fa07d0-5a0a-40ec-94f2-3d0db4aef2aa
-- title:
--   Lemma 9.3, p. 44 — an irreducible instance has a quasi-backbone of weight ≤ (α_S + 3) value(I)
-- statement:
--   Fix $\delta\in(1/2,1)$. Let $\alpha_S$ be a constant such that every singleton laminarly-weighted instance $I'$ (on any finite vertex and edge sets, with at least two vertices) has a tour of weight at most $\alpha_S\,\mathrm{value}(I')$. Let $I=(G,\mathcal L,x,y)$ be a laminarly-weighted ATSP instance on at least two vertices that is irreducible with respect to $\delta$. Then there is a subtour $B$ that is a **quasi-backbone**, i.e. $2\sum_{S\in\mathcal L^*}y_S\le(1-\delta)\,\mathrm{value}(I)$ with $\mathcal L^*=\{S\in\mathcal L: S\cap V(B)=\emptyset\}$, and
--   $$w_I(B)\le(\alpha_S+3)\,\mathrm{value}(I).$$
--
--   The quasi-backbone is the starting point of the proof of Theorem 9.4: it visits most of the dual value, so that the vertebrate-pair algorithm can be applied.
--
--   **Formalization Note** The paper states this result for a polynomial-time algorithm. Running times are not formalized: following §11 of the paper, which derives the integrality gap "non-constructively", the algorithm is read existentially, i.e. as the existence of the object the algorithm would return. The page takes $\alpha_S$ to be "the approximation guarantee for singleton instances as in Corollary 5.2" ($18+\varepsilon$); here $\alpha_S$ is any constant with the stated guarantee, posed as a hypothesis quantified over instances on all finite types, which is how §11 substitutes $\alpha'_S=10$. The range $\delta\in(1/2,1)$ is the paper's standing range for $\delta$ (Def. 8.1). The instance is required to have at least two vertices.
-- source:
--   Svensson, Tarnawski, Végh, A constant-factor approximation algorithm for the asymmetric traveling salesman problem, J. ACM 67(6) (2020), accepted manuscript (LSE Research Online 106582), p. 44, Lemma 9.3

import Mathlib
import Definitions.Def_ConstATSP_Gap_Graph
import Definitions.Def_ConstATSP_Gap_Instance

namespace ConstATSP.Gap

theorem lemma_9_3 (δ : ℝ) (hδ1 : 1 / 2 < δ) (hδ2 : δ < 1) (αS : ℝ)
    (hAS : ∀ {V' E' : Type} [Fintype V'] [DecidableEq V'] [Fintype E'] (I' : Instance V' E'),
      I'.IsValid → I'.IsSingleton → ∃ F : E' → ℕ, IsTour I'.G F ∧ I'.wt F ≤ αS * I'.value)
    {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    (I : Instance V E) (hI : I.IsValid) (hirr : I.IsIrreducible δ) :
    ∃ B : E → ℕ, I.IsQuasiBackbone δ B ∧ I.wt B ≤ (αS + 3) * I.value := by sorry

end ConstATSP.Gap
