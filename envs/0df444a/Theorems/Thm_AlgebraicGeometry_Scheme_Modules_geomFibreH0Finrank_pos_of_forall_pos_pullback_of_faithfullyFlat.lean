-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_pos_of_forall_pos_pullback_of_faithfullyFlat
-- name    : AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_pos_of_forall_pos_pullback_of_faithfullyFlat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/f4fbf136-5b3a-50fd-817e-644892c97d9f
-- title:
--   Positivity of geometric-fibre h⁰ descends along faithfully flat base change
-- statement:
--   Let $S$ and $S'$ be commutative rings in a fixed universe, with $S'$ an $S$-algebra that is faithfully flat as an $S$-module. Let $f : A \to \operatorname{Spec} S$ be a proper morphism of schemes and $f' : A' \to \operatorname{Spec} S'$ a morphism, and let $g : A' \to A$ be such that the square formed by $g$, $f'$, $f$ and $\operatorname{Spec}$ of the structure map $S \to S'$ is cartesian. Let $M$ be a module over $A$ which is invertible in the sense that every point of $A$ has an open neighbourhood $U$ such that the pullback of $M$ along the inclusion $U \hookrightarrow A$ is isomorphic to the unit module over $U$. Assume that for every algebraically closed field $k'$ and every ring homomorphism $sk' : S' \to k'$ the invariant `Scheme.Modules.geomFibreH0Finrank` of $f'$ and the pullback $g^{*}M$ at $(k', sk')$ is positive; that is, the $k'$-rank of the global sections of the pullback of $g^{*}M$ to the fibre product of $f'$ with $\operatorname{Spec} k' \to \operatorname{Spec} S'$ is nonzero. Then for every algebraically closed field $k$ and every ring homomorphism $sk : S \to k$, the corresponding invariant `Scheme.Modules.geomFibreH0Finrank` of $f$ and $M$ at $(k, sk)$ is positive.
--
--   This is the descent, along a faithfully flat ring extension, of the condition that an invertible module have a nonzero space of sections on every geometric fibre of a proper morphism; the essential point is that every geometric point of $\operatorname{Spec} S$ lifts to a geometric point of $\operatorname{Spec} S'$. It supplies the positivity clause needed when a canonical polarisation on a fake elliptic curve is recognised after a faithfully flat base change, and is cited by [`CerednikDrinfeld.QM.FakeEllipticCurve.isCanonicalPol_of_locIsoOnBase_pullback_of_faithfullyFlat`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.isCanonicalPol_of_locIsoOnBase_pullback_of_faithfullyFlat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_pos_of_forall_pos_pullback_of_faithfullyFlat.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_pos_of_forall_pos_pullback_of_faithfullyFlat
    {S S' : Type u} [CommRing S] [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {A A' : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) [IsProper f] (f' : A' ⟶ Spec (CommRingCat.of S'))
    (g : A' ⟶ A) (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    (h : ∀ (k' : Type u) [Field k'] [IsAlgClosed k'] (sk' : S' →+* k'),
      0 < Scheme.Modules.geomFibreH0Finrank f' ((Scheme.Modules.pullback g).obj M) k' sk')
    (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) :
    0 < Scheme.Modules.geomFibreH0Finrank f M k sk := by sorry
