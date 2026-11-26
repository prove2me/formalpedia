-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_AffineProEt_exists_isWeaklyContractible_cover
-- name    : AlgebraicGeometry.Scheme.AffineProEt.exists_isWeaklyContractible_cover
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T12:36:55.266398+00:00
-- url     : https://prove2.me/theorems/4935ea39-07b6-4c01-9058-eb389f0ae0e0
-- title:
--   Proposition 4.2.8 (affine form) — every pro-étale affine is covered by a weakly contractible one
-- statement:
--   Let $X$ be a scheme. Its **pro-étale site** $X_{\text{proét}}$ is the category of weakly étale $X$-schemes with the pro-étale topology, and $X_{\text{ét}}$ is its small étale site. Let $X^{\mathrm{aff}}_{\text{proét}}$ be the category of pro-étale affines over $X$. Call an object $W$ of it **weakly contractible** if every morphism $V \to W$ of pro-étale affines that is surjective on underlying spaces admits a section.
--
--   For every pro-étale affine $U$ there exist a weakly contractible pro-étale affine $W$ and a morphism $q : W \to U$ over $X$ that is surjective on underlying spaces.
--
--   This gives the pro-étale site a basis of objects on which every cover splits, so that higher cohomology of sheaves vanishes on them.
--
--   **Formalization Note** The paper's Proposition 4.2.8 is a statement about the topos (every object receives a surjection from a coproduct of coherent weakly contractible objects, where weak contractibility refers to surjections of sheaves). The Lean statement quantifies only over pro-étale affines and over surjective morphisms of schemes between them.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014), Proposition 4.2.8 (p. 29 of the arXiv v2 PDF) states that Shv(X_proét) is locally weakly contractible (Definition 3.2.1); the statement here is the affine form established in its proof, see also Theorem 1.5. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/Comparison/WeaklyContractible.lean, lines 157-205 (`AlgebraicGeometry.Scheme.AffineProEt.exists_isWeaklyContractible_cover`).

import Mathlib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Ind
import Definitions.Def_ProEtale_Morphisms_ProAffineEtale
import Definitions.Def_ProEtale_Topology_Comparison_Affine
import Definitions.Def_ProEtale_Topology_Comparison_WeaklyContractible

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

universe u
open CategoryTheory Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.AffineProEt
variable {S : Scheme.{u}}

theorem AlgebraicGeometry.Scheme.AffineProEt.exists_isWeaklyContractible_cover (U : S.AffineProEt) :
    ∃ (W : S.AffineProEt) (q : W ⟶ U), Surjective q.left ∧ W.IsWeaklyContractible := by sorry
