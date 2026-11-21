-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_relative_constant_etale_cohomology_succ_equiv_of_proper_excision
-- name    : AlgebraicGeometry.Scheme.nonempty_relative_constant_etale_cohomology_succ_equiv_of_proper_excision
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-20T19:48:49.846079+00:00
-- url     : https://prove2.me/theorems/6817ae0e-82a7-4faa-9fc3-6e3d23867ec0
-- title:
--   Positive-degree relative étale cohomology under proper excision
-- statement:
--   Let $f\colon Y\to X$ be proper and an isomorphism outside the image of a closed immersion $i\colon Z\hookrightarrow X$. Put $E=Y\times_X Z$ and let $A$ be a finite abelian group. For every $q\geq 1$, there is an isomorphism
--   $$H^q_{\mathrm{et}}(X,F_{X,Z})\simeq H^q_{\mathrm{et}}(Y,F_{Y,E}),$$
--   where the relative constant sheaf $F_{X,Z}$ is the kernel of restriction to the closed direct image, and $F_{Y,E}$ is defined in the same way. These are the extension-by-zero cohomology groups of the common complementary open in the two schemes.
-- source:
--   Stacks Project, Theorem 59.91.11 (https://stacks.math.columbia.edu/tag/095T) and Lemma 59.70.8 (https://stacks.math.columbia.edu/tag/095L).

import Definitions.Def_AlgebraicGeometry_SmallEtaleRelativeConstant

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

theorem AlgebraicGeometry.Scheme.nonempty_relative_constant_etale_cohomology_succ_equiv_of_proper_excision
    (A : Type u) [AddCommGroup A] [Finite A] {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.Opens) [IsIso (f ∣_ U)] (hU : Set.range i = (U : Set X)ᶜ) (q : ℕ) :
    Nonempty ((PhilipponEtaleRelativeCohomology.relativeConstant i A).H (q + 1) ≃+
      (PhilipponEtaleRelativeCohomology.relativeConstant (pullback.fst f i) A).H (q + 1)) := by sorry
