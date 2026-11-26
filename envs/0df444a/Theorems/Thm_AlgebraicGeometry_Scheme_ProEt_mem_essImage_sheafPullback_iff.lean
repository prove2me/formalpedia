-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_ProEt_mem_essImage_sheafPullback_iff
-- name    : AlgebraicGeometry.Scheme.ProEt.mem_essImage_sheafPullback_iff
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T12:45:18.884474+00:00
-- url     : https://prove2.me/theorems/cc3a7961-2c2d-5197-86c9-6e131738614c
-- title:
--   Lemma 5.1.2 (second assertion) — the essential image of pullback consists of the classical sheaves
-- statement:
--   Let $X$ be a scheme. Its **pro-étale site** $X_{\text{proét}}$ is the category of weakly étale $X$-schemes with the pro-étale topology, and $X_{\text{ét}}$ is its small étale site. Let $\nu^* : \operatorname{Shv}(X_{\text{ét}}, A) \to \operatorname{Shv}(X_{\text{proét}}, A)$ be the pullback functor. A sheaf $G$ on $X_{\text{proét}}$ is isomorphic to $\nu^* F$ for some étale sheaf $F$ if and only if, for every pro-étale affine $U$ presented as a small cofiltered limit $U = \varprojlim_i U_i$ of affine schemes étale over $X$,
--
--   $$
--   G(U) \;=\; \varinjlim_i G(U_i),
--   $$
--
--   that is, $G$ sends such limits to colimits.
--
--   Sheaves in this essential image are the *classical* sheaves; the criterion is how one recognises that a pro-étale sheaf comes from the étale site.
--
--   **Formalization Note** The right-hand condition is `Functor.PreservesRelativeFilteredColimits` for the inclusion of affine étale schemes into pro-étale affines: for every small cofiltered diagram of affine étale schemes and every limit cone over its image in pro-étale affines, $G$ maps that cone to a colimit cocone. Coefficients are a category $A$ as in the full faithfulness statements.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014), Lemma 5.1.2 (p. 34 of the arXiv v2 PDF), second assertion; the word 'classical' is Definition 5.1.3. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/Comparison/Classical.lean, lines 141-154 (`AlgebraicGeometry.Scheme.ProEt.mem_essImage_sheafPullback_iff`).

import Mathlib
import Definitions.Def_ProEtale_Comparator_Definitions
import Definitions.Def_ProEtale_Algebra_Etale
import Definitions.Def_ProEtale_Algebra_FaithfullyFlat
import Definitions.Def_ProEtale_Algebra_Ind
import Definitions.Def_ProEtale_Algebra_IndEtale
import Definitions.Def_ProEtale_Algebra_IndWeaklyEtale
import Definitions.Def_ProEtale_Algebra_WeaklyEtale
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_AlgCat_FilteredColimits
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits
import Definitions.Def_ProEtale_Mathlib_Algebra_Homology_ShortComplex_Exact
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Ind
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty
import Definitions.Def_ProEtale_Mathlib_RingTheory_Ideal_Pure
import Definitions.Def_ProEtale_Morphisms_ProAffineEtale
import Definitions.Def_ProEtale_Morphisms_WeaklyEtale
import Definitions.Def_ProEtale_Pro_Basic
import Definitions.Def_ProEtale_Topology_Comparison_Affine

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

universe w u
open CategoryTheory Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProEt
variable (S : Scheme.{u}) (A : Type*) [Category A] [HasColimitsOfSize.{u, u + 1} A]
  [HasFilteredColimitsOfSize.{u, u} A] [AB5OfSize.{u, u} A] [HasLimitsOfSize.{u, u + 1} A]
  [HasWeakSheafify (ProEt.topology S) A] [HasWeakSheafify (AffineProEt.topology S) A]
  [(ProEt.sheafPushforward S A).IsRightAdjoint]
variable {S A}

theorem AlgebraicGeometry.Scheme.ProEt.mem_essImage_sheafPullback_iff (G : Sheaf (ProEt.topology S) A) :
    (sheafPullback S A).essImage G ↔
      Functor.PreservesRelativeFilteredColimits.{u} (AffineEtale.toAffineProEt S)
        ((AffineProEt.toProEt S).op ⋙ G.obj) := by sorry
