-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_isZero_relative_constant_etale_higher_direct_image_of_proper_excision
-- name    : AlgebraicGeometry.Scheme.isZero_relative_constant_etale_higher_direct_image_of_proper_excision
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-20T20:18:30.73672+00:00
-- url     : https://prove2.me/theorems/ba9bb3bb-6ee9-4deb-bad6-4f5eada1173a
-- title:
--   Vanishing of higher direct images for relative constants under proper excision
-- statement:
--   Let $f\colon Y\to X$ be proper and an isomorphism over the complement of a closed immersion $Z\hookrightarrow X$. Set $E=Y\times_X Z$ and let $A$ be a finite abelian group. For the relative constant sheaf $F_{Y,E}$, the kernel of restriction of the constant sheaf to the direct image from $E$, one has
--   $$R^jf_* F_{Y,E}=0\qquad(j>0).$$
--   This is the higher direct-image assertion used to compare relative étale cohomology under proper excision.
-- source:
--   Stacks Project, https://stacks.math.columbia.edu/tag/095T and https://stacks.math.columbia.edu/tag/095L.

import Definitions.Def_AlgebraicGeometry_SmallEtaleRelativeConstant
import Mathlib.CategoryTheory.Abelian.RightDerived

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem AlgebraicGeometry.Scheme.isZero_relative_constant_etale_higher_direct_image_of_proper_excision
    (A : Type u) [AddCommGroup A] [Finite A] {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.Opens) [IsIso (f ∣_ U)] (hU : Set.range i = (U : Set X)ᶜ) (q : ℕ) :
    IsZero (((PhilipponEtaleClosedPushforward.pushforward f).rightDerived (q + 1)).obj
      (PhilipponEtaleRelativeCohomology.relativeConstant (pullback.fst f i) A)) := by sorry
