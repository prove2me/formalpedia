-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_ProEt_nonempty_continuousH_addEquiv_H_limit
-- name    : AlgebraicGeometry.Scheme.ProEt.nonempty_continuousH_addEquiv_H_limit
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T12:46:35.171448+00:00
-- url     : https://prove2.me/theorems/bafd6173-28e7-59c5-b239-31d407750cf8
-- title:
--   Proposition 5.6.2 — continuous étale cohomology is pro-étale cohomology of the limit
-- statement:
--   Let $X$ be a scheme. Its **pro-étale site** $X_{\text{proét}}$ is the category of weakly étale $X$-schemes with the pro-étale topology, and $X_{\text{ét}}$ is its small étale site. Let $(F_n)_{n \in \mathbb N}$ be an inverse system of sheaves of abelian groups on $X_{\text{ét}}$ whose transition maps $F_{n+1} \to F_n$ are epimorphisms. Its **continuous étale cohomology** $H^i_{\mathrm{cont}}(X_{\text{ét}}, (F_n))$ is the $i$-th right derived functor of $(F_n) \mapsto H^0(X_{\text{ét}}, \varprojlim_n F_n)$ on the category of inverse systems. Then for every $i \ge 0$ there is an isomorphism of abelian groups
--
--   $$
--   H^i_{\mathrm{cont}}\bigl(X_{\text{ét}}, (F_n)\bigr) \;\cong\; H^i\bigl(X_{\text{proét}}, \varprojlim_n \nu^* F_n\bigr),
--   $$
--
--   where the limit on the right is the inverse limit of sheaves on $X_{\text{proét}}$.
--
--   This identifies Jannsen's continuous étale cohomology with the cohomology of a single sheaf on the pro-étale site.
--
--   **Formalization Note** Two differences from the paper. The Lean statement asserts existence of an additive isomorphism, `Nonempty (_ ≃+ _)`, where the paper gives a canonical identification. Continuous cohomology `continuousH S F i` is defined as the group $\operatorname{Ext}^i$ from the constant system on the constant sheaf $\mathbb Z$ to $(F_n)$ in the category of inverse systems, which computes the derived functor above.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014), Proposition 5.6.2 (p. 41 of the arXiv v2 PDF; Section 5.6 does not exist in arXiv v1), with Definition 5.6.1 after Jannsen, Continuous étale cohomology, §3. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/Comparison/ContinuousComparison.lean, lines 276-406 (`AlgebraicGeometry.Scheme.ProEt.nonempty_continuousH_addEquiv_H_limit`).

import Mathlib
import Definitions.Def_ProEtale_Comparator_Definitions
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Sites_EtaleCohomology
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Abelian_SequentialSystem
import Definitions.Def_ProEtale_Topology_Comparison_ContinuousComparison
import Definitions.Def_ProEtale_Topology_Comparison_RepleteExact
import Definitions.Def_ProEtale_Topology_Proetale_Sheafification

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

universe u
open CategoryTheory Limits Opposite Abelian
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
variable (S : Scheme.{u})
open AlgebraicGeometry.Scheme.ProEt
variable {S}
universe v₁ u₁

theorem AlgebraicGeometry.Scheme.ProEt.nonempty_continuousH_addEquiv_H_limit
    (F : ℕᵒᵖ ⥤ Sheaf S.smallEtaleTopology Ab.{u + 1})
    (hF : ∀ n, Epi (SequentialSystem.transition F n)) (i : ℕ) :
    Nonempty (continuousH S F i ≃+
      Sheaf.H (limit (F ⋙ ProEt.sheafPullback S Ab.{u + 1})) i) := by sorry
