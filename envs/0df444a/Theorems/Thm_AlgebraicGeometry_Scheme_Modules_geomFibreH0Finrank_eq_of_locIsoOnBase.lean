-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_locIsoOnBase
-- name    : AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_eq_of_locIsoOnBase
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/8d506484-efea-5e50-8d1d-64a4ea9187dd
-- title:
--   Geometric-fibre h⁰ is invariant under local isomorphism on the base
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$ a morphism, and let $M, M'$ be modules on $A$ (objects of `A.Modules`). Assume `LocIsoOnBase f M M'`, i.e. for every point $s$ of $\operatorname{Spec} S$ there is an open subset $U \subseteq \operatorname{Spec} S$ containing $s$ such that the pullbacks of $M$ and of $M'$ along the open immersion $f^{-1}U \hookrightarrow A$ are isomorphic as modules on $f^{-1}U$ (the isomorphism type is merely asserted to be nonempty, so no coherence between the isomorphisms for different $s$ is required). Let $k$ be a field and $sk : S \to k$ a ring homomorphism. The conclusion is the equality of natural numbers $$\mathrm{geomFibreH0Finrank}\,f\,M\,k\,sk = \mathrm{geomFibreH0Finrank}\,f\,M'\,k\,sk,$$ where `Scheme.Modules.geomFibreH0Finrank f M k sk` is the `Module.finrank` over $k$ of the global sections of the pullback of $M$ along the first projection of the fibre product of $f$ with $\operatorname{Spec}(sk)$, the $k$-module structure coming from the $k$-algebra structure on the global sections of that fibre product induced by the second projection.
--
--   This is the statement that the dimension $h^0$ of the space of global sections on a geometric fibre depends only on the isomorphism class of the module locally over the base. It is used for the positivity and multiplicativity clauses in the theory of polarisation data on abelian schemes, and in the construction of Hilbert-type representing schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_locIsoOnBase.lean

import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

universe u

theorem AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_eq_of_locIsoOnBase
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) {M M' : A.Modules}
    (h : LocIsoOnBase f M M') (k : Type u) [Field k] (sk : S →+* k) :
    Scheme.Modules.geomFibreH0Finrank f M k sk = Scheme.Modules.geomFibreH0Finrank f M' k sk := by sorry
