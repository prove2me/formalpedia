-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_smallEtale_additive_succ_equiv_orderedCech_of_acyclic_intersections
-- name    : AlgebraicGeometry.Scheme.smallEtale_additive_succ_equiv_orderedCech_of_acyclic_intersections
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-20T00:25:22.198186+00:00
-- url     : https://prove2.me/theorems/353d1529-0e50-41b8-87f8-ce13e38a82e4
-- title:
--   Positive additive étale cohomology via an acyclic ordered affine cover
-- statement:
--   Let $X$ be a scheme over a field $K$, and let $\mathcal U$ be a finite ordered affine open cover. Suppose every intersection indexed by a strictly increasing tuple from $\mathcal U$ has zero positive-degree additive étale cohomology. Then for every $i>0$ there is a $K$-linear isomorphism
--   $$H^i_{\mathrm{et}}(X,\mathbf G_a)\simeq\check H^i(\mathcal U,\mathcal O_X).$$
--   The right hand side uses alternating restrictions on strictly increasing tuples. Scalar multiplication on the left comes from multiplying sections by elements of $K$.
-- source:
--   Stacks Project, Lemma 21.10.7 in https://stacks.math.columbia.edu/tag/03AV, with the ordered Čech complex of Lemma 20.23.6, https://stacks.math.columbia.edu/tag/01FM. See also the separated-scheme proof of Theorem 59.22.4, https://stacks.math.columbia.edu/tag/03P2.

import Definitions.Def_AlgebraicGeometry_SmallEtaleAdditive
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

universe u

theorem AlgebraicGeometry.Scheme.smallEtale_additive_succ_equiv_orderedCech_of_acyclic_intersections
    (K : Type u) [Field K] {X : Scheme.{u}} (π : X ⟶ Spec (.of K))
    (U : X.OrderedAffineCover)
    (hU : ∀ (m : ℕ) (s : U.Idx m) (q : ℕ),
      Subsingleton ((SmallEtaleAdditive.sheaf (U.inter s : Scheme.{u})).H (q + 1))) :
    letI : ∀ q : ℕ, Module K ((SmallEtaleAdditive.sheaf X).H q) :=
      fun q => SmallEtaleAdditive.cohomologyModule π q
    ∀ q : ℕ, Nonempty (((SmallEtaleAdditive.sheaf X).H (q + 1)) ≃ₗ[K]
      (OModulePresheaf.unit π).HSucc U q) := by sorry
