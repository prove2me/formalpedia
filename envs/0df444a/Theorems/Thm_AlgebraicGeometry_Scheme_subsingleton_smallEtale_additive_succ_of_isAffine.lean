-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_subsingleton_smallEtale_additive_succ_of_isAffine
-- name    : AlgebraicGeometry.Scheme.subsingleton_smallEtale_additive_succ_of_isAffine
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-20T00:25:40.04619+00:00
-- url     : https://prove2.me/theorems/f6e42101-8930-4d51-8d76-5e17d2e66667
-- title:
--   Vanishing of positive additive étale cohomology on affine schemes
-- statement:
--   If $Y$ is an affine scheme, the additive sheaf on the small étale site satisfies
--   $$H^i_{\mathrm{et}}(Y,\mathbf G_a)=0\qquad (i>0).$$
--   The sheaf assigns the additive group of global functions to every étale object.
-- source:
--   Stacks Project, Theorem 59.22.4, affine vanishing in the proof, https://stacks.math.columbia.edu/tag/03P2.

import Definitions.Def_AlgebraicGeometry_SmallEtaleAdditive

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

universe u

theorem AlgebraicGeometry.Scheme.subsingleton_smallEtale_additive_succ_of_isAffine
    (X : Scheme.{u}) [IsAffine X] (q : ℕ) :
    Subsingleton ((SmallEtaleAdditive.sheaf X).H (q + 1)) := by sorry
