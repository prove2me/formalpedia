-- Prove2me | Theorems.Thm_CvxComposite_Conj_lemma_6
-- name    : CvxComposite.Conj.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:41.399313+00:00
-- url     : https://prove2.me/theorems/efc3ae74-9714-4e2e-9d60-66865a69254a
-- title:
--   Lemma 6(a)–(b), p. 7 — support functions of the K-epigraph and graph
-- statement:
--   Let $F:E_1\to E_2^\bullet$ be a partial map and let $K\subseteq E_2$ be a closed convex cone. Write $D=\operatorname{dom}F$, $K\text{-epi}F$ for its $K$-epigraph, $\operatorname{gph}F$ for its graph, $K^\circ$ for the polar cone, and $\delta_{K^\circ}$ for its indicator. For every $(u,v)\in E_1\times E_2$,
--   $$
--   \sigma_{K\text{-epi}F}(u,v)=\sigma_{\operatorname{gph}F}(u,v)+\delta_{K^\circ}(v),\qquad
--   \sigma_{\operatorname{gph}F}(u,-v)=\langle v,F\rangle^*(u).
--   $$
--
--   These identities connect support functions of the epigraph to conjugates of scalarizations, which are the terms in Theorem 12.
--
--   **Formalization Note** The map is represented by $(D,F)$; no nonempty-domain hypothesis is added. Pairings on $E_1\times E_2$ are sums of the component pairings. Part (c), which concerns linear $F$, is outside this item.
-- source:
--   Burke, Hoheisel & Nguyen, A Study of Convex Convex-Composite Functions via Infimal Convolution with Applications, arXiv:1907.08318v2, p. 7, Lemma 6(a)–(b)

import Mathlib
import Definitions.Def_CvxComposite_Conj_Setting
open scoped InnerProductSpace Pointwise

namespace CvxComposite.Conj

open MoreauProx.Characterization MoreauProx.Decomposition

/-- Lemma 6(a)–(b), p. 7: support functions of the K-epigraph and graph. -/
theorem lemma_6 {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    (K : Set E₂) (hK : IsClosedConvexCone K) (D : Set E₁) (F : E₁ → E₂) :
    (∀ u : E₁, ∀ v : E₂,
      suppKEpi K D F u v = suppGph D F u v + indicatorFn (polarCone K) v) ∧
    (∀ u : E₁, ∀ v : E₂,
      suppGph D F u (-v) = conj (scal v D F) u) := by sorry

end CvxComposite.Conj
