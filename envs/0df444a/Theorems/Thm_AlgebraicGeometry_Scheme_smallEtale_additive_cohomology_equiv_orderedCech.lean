-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_smallEtale_additive_cohomology_equiv_orderedCech
-- name    : AlgebraicGeometry.Scheme.smallEtale_additive_cohomology_equiv_orderedCech
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-19T21:56:21.230404+00:00
-- url     : https://prove2.me/theorems/fbfa529c-4d63-4264-b8f2-956a78e9c45d
-- title:
--   Additive étale cohomology via an ordered affine Čech cover
-- statement:
--   Let $X$ be a separated scheme over a field $K$, and let $\mathcal U$ be a finite ordered affine open cover of $X$. For each $q\geq 0$, there is a $K$-linear isomorphism
--   $$H^q_{\mathrm{et}}(X,\mathbf G_a)\simeq \check H^q(\mathcal U,\mathcal O_X).$$
--   On the small étale site $\mathbf G_a$ assigns to each object its additive group of global functions. Its cohomology has the scalar action induced by multiplication on sections. On the right, the differential uses the alternating restriction maps on strictly increasing tuples of cover indices.
-- source:
--   Stacks Project, Theorem 59.22.4 (étale–Zariski comparison), https://stacks.math.columbia.edu/tag/03P2, and Cohomology of Schemes, Lemma 30.2.6 (separated affine-cover comparison), cited in its proof.

import Definitions.Def_AlgebraicGeometry_SmallEtaleAdditive
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

universe u

theorem AlgebraicGeometry.Scheme.smallEtale_additive_cohomology_equiv_orderedCech
    (K : Type u) [Field K] {X : Scheme.{u}} (π : X ⟶ Spec (.of K)) [IsSeparated π]
    (U : X.OrderedAffineCover) :
    letI : ∀ q : ℕ, Module K ((SmallEtaleAdditive.sheaf X).H q) :=
      fun q => SmallEtaleAdditive.cohomologyModule π q
    Nonempty (((SmallEtaleAdditive.sheaf X).H 0) ≃ₗ[K] (OModulePresheaf.unit π).H0 U) ∧
      ∀ q : ℕ, Nonempty (((SmallEtaleAdditive.sheaf X).H (q + 1)) ≃ₗ[K]
        (OModulePresheaf.unit π).HSucc U q) := by sorry
