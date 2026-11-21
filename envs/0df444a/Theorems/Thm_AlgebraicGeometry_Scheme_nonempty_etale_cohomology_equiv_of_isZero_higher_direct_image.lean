-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_etale_cohomology_equiv_of_isZero_higher_direct_image
-- name    : AlgebraicGeometry.Scheme.nonempty_etale_cohomology_equiv_of_isZero_higher_direct_image
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-20T20:18:40.619174+00:00
-- url     : https://prove2.me/theorems/26f659b5-41f1-4de5-85be-aba2673cb784
-- title:
--   Étale cohomology of a sheaf with zero higher direct images
-- statement:
--   Let $f\colon Y\to X$ be a morphism of schemes and $F$ an abelian sheaf on the small étale site of $Y$. Assume that $R^jf_*F=0$ for all $j>0$. Then for every $n\geq0$ there is an isomorphism
--   $$H^n_{\mathrm{et}}(X,f_*F)\simeq H^n_{\mathrm{et}}(Y,F).$$
--   This is the acyclic case of the étale Leray comparison.
-- source:
--   Stacks Project, Leray spectral sequence, https://stacks.math.columbia.edu/tag/03QC.

import Definitions.Def_AlgebraicGeometry_SmallEtaleAbelianDirectImage
import Mathlib.CategoryTheory.Abelian.RightDerived

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem AlgebraicGeometry.Scheme.nonempty_etale_cohomology_equiv_of_isZero_higher_direct_image
    {X Y : Scheme.{u}} (f : Y ⟶ X) (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (h : ∀ q : ℕ, IsZero (((PhilipponEtaleClosedPushforward.pushforward f).rightDerived (q + 1)).obj F)) (n : ℕ) :
    Nonempty (((PhilipponEtaleClosedPushforward.pushforward f).obj F).H n ≃+ F.H n) := by sorry
