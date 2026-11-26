-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_AffineProEt_isCoverDense_toProEt
-- name    : AlgebraicGeometry.Scheme.AffineProEt.isCoverDense_toProEt
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T12:32:45.758251+00:00
-- url     : https://prove2.me/theorems/e09dc415-ee08-5586-805f-9118abd4cf06
-- title:
--   Lemma 4.2.4 (second assertion) — pro-étale affines generate the pro-étale site
-- statement:
--   Let $X$ be a scheme. Its **pro-étale site** $X_{\text{proét}}$ is the category of weakly étale $X$-schemes with the pro-étale topology, and $X_{\text{ét}}$ is its small étale site. A **pro-étale affine** is an object of $X_{\text{proét}}$ that can be written as a small cofiltered limit of affine schemes étale over $X$; these form a full subcategory $X^{\mathrm{aff}}_{\text{proét}} \subseteq X_{\text{proét}}$.
--
--   The inclusion $X^{\mathrm{aff}}_{\text{proét}} \hookrightarrow X_{\text{proét}}$ is **cover-dense** for the pro-étale topology: for every object $Y$ of $X_{\text{proét}}$, the morphisms $U \to Y$ whose source is a pro-étale affine generate a covering sieve of $Y$.
--
--   Consequently sheaves on $X_{\text{proét}}$ are determined by their restriction to pro-étale affines, which is how every local computation on the pro-étale site is carried out.
--
--   **Formalization Note** The statement is `(AffineProEt.toProEt S).IsCoverDense (ProEt.topology S)`. `S.AffineProEt` is defined as the category of $S$-schemes whose structure morphism lies in the pro-completion of the class of étale morphisms with affine source.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014), Lemma 4.2.4 (p. 29 of the arXiv v2 PDF), second assertion. The first assertion (the site is subcanonical) is not part of this statement. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/Comparison/Affine.lean, lines 152-263 (`AlgebraicGeometry.Scheme.AffineProEt.isCoverDense_toProEt`).

import Mathlib
import Definitions.Def_ProEtale_Algebra_Etale
import Definitions.Def_ProEtale_Algebra_FaithfullyFlat
import Definitions.Def_ProEtale_Algebra_Ind
import Definitions.Def_ProEtale_Algebra_IndEtale
import Definitions.Def_ProEtale_Algebra_IndWeaklyEtale
import Definitions.Def_ProEtale_Algebra_WeaklyEtale
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_AlgCat_FilteredColimits
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits
import Definitions.Def_ProEtale_Mathlib_Algebra_Homology_ShortComplex_Exact
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Ind
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty
import Definitions.Def_ProEtale_Mathlib_RingTheory_Ideal_Pure
import Definitions.Def_ProEtale_Morphisms_ProAffineEtale
import Definitions.Def_ProEtale_Morphisms_WeaklyEtale
import Definitions.Def_ProEtale_Topology_Comparison_Affine

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

universe w u
open CategoryTheory MorphismProperty Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
variable {S : Scheme.{u}}
variable (S : Scheme.{u})
variable (A : Type*) [Category A]
open AlgebraicGeometry.Scheme.AffineProEt
variable {S}

theorem AlgebraicGeometry.Scheme.AffineProEt.isCoverDense_toProEt : (toProEt S).IsCoverDense (ProEt.topology S) := by sorry
