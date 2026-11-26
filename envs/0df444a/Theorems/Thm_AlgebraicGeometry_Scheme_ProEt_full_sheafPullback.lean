-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_ProEt_full_sheafPullback
-- name    : AlgebraicGeometry.Scheme.ProEt.full_sheafPullback
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T12:44:47.171516+00:00
-- url     : https://prove2.me/theorems/99581f3f-3fd9-42c0-899a-6dba16d35c77
-- title:
--   Lemma 5.1.2 (first assertion) — pullback from the étale to the pro-étale site is full
-- statement:
--   Let $X$ be a scheme. Its **pro-étale site** $X_{\text{proét}}$ is the category of weakly étale $X$-schemes with the pro-étale topology, and $X_{\text{ét}}$ is its small étale site. The inclusion $X_{\text{ét}} \to X_{\text{proét}}$ induces a pullback functor on sheaves
--
--   $$
--   \nu^* : \operatorname{Shv}(X_{\text{ét}}, A) \longrightarrow \operatorname{Shv}(X_{\text{proét}}, A),
--   $$
--
--   left adjoint to restriction $\nu_*$. The functor $\nu^*$ is **full**: every morphism $\nu^* F \to \nu^* G$ of pro-étale sheaves comes from a morphism $F \to G$ of étale sheaves.
--
--   Together with faithfulness this is the full faithfulness of $\nu^*$ in Lemma 5.1.2.
--
--   **Formalization Note** Same generality as the faithfulness statement: sheaves with values in a category $A$ with the required limits, colimits, exact filtered colimits and sheafification, where the paper treats sheaves of sets.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014), Lemma 5.1.2 (p. 34 of the arXiv v2 PDF), first assertion, fullness. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/Comparison/Affine.lean, lines 1702-1703 (`AlgebraicGeometry.Scheme.ProEt.full_sheafPullback`).

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
variable {A} [HasColimitsOfSize.{u, u + 1} A] [HasFilteredColimitsOfSize.{u, u} A]
  [AB5OfSize.{u, u} A]
open AlgebraicGeometry.Scheme.ProEt
variable [HasLimitsOfSize.{u, u + 1} A] [HasWeakSheafify (ProEt.topology S) A]
  [HasWeakSheafify (AffineProEt.topology S) A]
  [(ProEt.sheafPushforward S A).IsRightAdjoint]

theorem AlgebraicGeometry.Scheme.ProEt.full_sheafPullback : (sheafPullback S A).Full := by sorry
