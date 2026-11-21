-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_etale_cohomology_equiv_closed_direct_image
-- name    : AlgebraicGeometry.Scheme.nonempty_etale_cohomology_equiv_closed_direct_image
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-20T18:51:45.148171+00:00
-- url     : https://prove2.me/theorems/69cd151a-f623-428c-a823-2a16bc76f644
-- title:
--   Étale cohomology of the direct image under a closed immersion
-- statement:
--   Let $i\colon Z\to X$ be a closed immersion of schemes,
--   and let $F$ be an abelian sheaf on the small étale site of $Z$. For every $q\geq 0$ there is
--   an isomorphism
--   $$H^q_{\mathrm{et}}(Z,F)\simeq H^q_{\mathrm{et}}(X,i_*F).$$
--   This identifies cohomology on a closed subscheme with cohomology of its direct image.
-- source:
--   Stacks Project, Proposition 59.55.2, https://stacks.math.columbia.edu/tag/03QP, specialized to closed immersions.

import Definitions.Def_AlgebraicGeometry_SmallEtaleAbelianDirectImage

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

universe u

theorem AlgebraicGeometry.Scheme.nonempty_etale_cohomology_equiv_closed_direct_image
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ) :
    Nonempty (F.H q ≃+ ((PhilipponEtaleClosedPushforward.pushforward i).obj F).H q) := by sorry
