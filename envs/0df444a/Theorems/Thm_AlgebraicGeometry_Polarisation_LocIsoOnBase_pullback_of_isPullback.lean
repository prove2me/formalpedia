-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_isPullback
-- name    : AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/c2b4344f-937a-5890-98f1-791a2e30448d
-- title:
--   Local isomorphism over the base is stable under base change
-- statement:
--   Let $\varphi : S \to S'$ be a homomorphism of commutative rings, let $A, A'$ be schemes, let $f : A \to \operatorname{Spec} S$ and $f' : A' \to \operatorname{Spec} S'$ be morphisms, and let $g : A' \to A$ be a morphism such that the square with sides $g$, $f'$, $f$ and $\operatorname{Spec}(\varphi)$ is cartesian in the category of schemes. Let $M, M'$ be $\mathcal{O}_A$-modules, and suppose $M$ and $M'$ satisfy `LocIsoOnBase f M M'`, that is: for every point $s$ of $\operatorname{Spec} S$ there is an open $U \subseteq \operatorname{Spec} S$ with $s \in U$ such that the restrictions of $M$ and $M'$ along the open immersion $f^{-1}(U) \hookrightarrow A$ are isomorphic as $\mathcal{O}_{f^{-1}(U)}$-modules. The conclusion is `LocIsoOnBase f' (g^*M) (g^*M')`: for every point $s'$ of $\operatorname{Spec} S'$ there is an open $U' \ni s'$ in $\operatorname{Spec} S'$ such that the restrictions of the pullbacks $g^*M$ and $g^*M'$ along $f'^{-1}(U') \hookrightarrow A'$ are isomorphic. The proof uses only the commutativity of the square, not its universal property.
--
--   This is the base-change stability of the relation 'the two modules become isomorphic over an open cover of the base', the relation used to compare a polarisation with its translates and duals up to line bundles pulled back from the base. It is invoked when polarisation data are transported along a cartesian square, for instance in the corresponding statement for symmetry of polarisations and in the descent and closed-immersion criteria for polarised abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_isPullback.lean

import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

universe u

theorem AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_isPullback
    {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S')} {g : A' ⟶ A}
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    {M M' : A.Modules} (h : LocIsoOnBase f M M') :
    LocIsoOnBase f' ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj M') := by sorry
