-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
-- name    : AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/67a2aa33-8854-5a84-813d-6a0059b9d8e6
-- title:
--   Local isomorphy over the base is an equivalence relation
-- statement:
--   Let $S$ be a commutative ring, let $X$ be a scheme (in a fixed universe) and let $g \colon X \to \operatorname{Spec} S$ be a morphism of schemes, where $\operatorname{Spec} S$ is the spectrum of $S$ viewed as a commutative ring object. Consider the binary relation `LocIsoOnBase g` on the objects of `X.Modules`, the category of module sheaves on $X$: two such objects $M$, $M'$ are related exactly when for every point $s$ of the underlying space of $\operatorname{Spec} S$ there is an open subset $U \subseteq \operatorname{Spec} S$ with $s \in U$ such that the pullbacks of $M$ and of $M'$ along the open immersion $g^{-1}U \hookrightarrow X$ are isomorphic, i.e. the type of isomorphisms between the images of $M$ and $M'$ under the pullback functor `Scheme.Modules.pullback (g ⁻¹ᵁ U).ι` is nonempty. The assertion is that this relation is an `Equivalence`: it is reflexive, symmetric and transitive on the objects of `X.Modules`.
--
--   This records that being isomorphic Zariski-locally over the base is an equivalence relation on module sheaves on $X$, so that it may be used freely as a substitute for genuine isomorphy in the theory of polarisations of abelian schemes; it is invoked throughout that development, for instance in the treatment of symmetry of line bundles and of two-torsion kernels.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence.lean

import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Polarisation

universe u

theorem AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence
    {S : Type u} [CommRing S] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of S)) :
    Equivalence (LocIsoOnBase g) := by sorry
