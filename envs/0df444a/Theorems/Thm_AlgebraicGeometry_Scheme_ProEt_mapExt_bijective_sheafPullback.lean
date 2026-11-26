-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_ProEt_mapExt_bijective_sheafPullback
-- name    : AlgebraicGeometry.Scheme.ProEt.mapExt_bijective_sheafPullback
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T12:45:47.278929+00:00
-- url     : https://prove2.me/theorems/f99f4a3e-ac0c-5cbf-8c2d-76c5e0991d45
-- title:
--   Corollary 5.1.9 (first assertion) — étale and pro-étale Ext groups agree
-- statement:
--   Let $X$ be a scheme. Its **pro-étale site** $X_{\text{proét}}$ is the category of weakly étale $X$-schemes with the pro-étale topology, and $X_{\text{ét}}$ is its small étale site. Let $\nu^* : \operatorname{Ab}(X_{\text{ét}}) \to \operatorname{Ab}(X_{\text{proét}})$ be the pullback functor on sheaves of abelian groups; it is exact. For abelian sheaves $F$, $K$ on $X_{\text{ét}}$ and every $n \ge 0$, the map induced by $\nu^*$
--
--   $$
--   \operatorname{Ext}^n_{X_{\text{ét}}}(F, K) \longrightarrow \operatorname{Ext}^n_{X_{\text{proét}}}(\nu^* F, \nu^* K)
--   $$
--
--   is bijective.
--
--   Taking $F$ constant gives the agreement of étale cohomology with pro-étale cohomology of the pulled-back sheaf, so no cohomological information is lost in passing to the pro-étale site.
--
--   **Formalization Note** The map is `Functor.mapExtAddHom` of the exact functor `ProEt.sheafPullback S Ab`, on `Abelian.Ext` groups; sheaves take values in `Ab.{u + 1}` for $X$ a `Scheme.{u}`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014), Corollary 5.1.9 (p. 35 of the arXiv v2 PDF), first assertion. The assertion that ν^*(Ab(X_ét)) is a Serre subcategory is not part of this statement. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/Comparison/CohomologyComparison.lean, lines 316-322 (`AlgebraicGeometry.Scheme.ProEt.mapExt_bijective_sheafPullback`).

import Mathlib
import Definitions.Def_ProEtale_Comparator_Definitions
import Definitions.Def_ProEtale_Topology_Comparison_CohomologyComparison
import Definitions.Def_ProEtale_Topology_Proetale_Sheafification

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

universe w t v u u₁ u₂ u₃ v₁ v₂ v₃
open CategoryTheory Limits Opposite Abelian
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
variable (S : Scheme.{u})
open AlgebraicGeometry.Scheme.ProEt
variable {S}

theorem AlgebraicGeometry.Scheme.ProEt.mapExt_bijective_sheafPullback (F K : Sheaf S.smallEtaleTopology Ab.{u + 1}) (n : ℕ) :
    Function.Bijective ((ProEt.sheafPullback S Ab.{u + 1}).mapExtAddHom F K n) := by sorry
