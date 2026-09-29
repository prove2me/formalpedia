-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_comp_eq_specMap_of_asIdeal_eq_bot_of_locallyOfFiniteType_of_isAlgClosed_of_injective
-- name    : AlgebraicGeometry.exists_comp_eq_specMap_of_asIdeal_eq_bot_of_locallyOfFiniteType_of_isAlgClosed_of_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/6142f8cb-5e18-5c71-b1b6-7a5315164e27
-- title:
--   A generic point spreads to a geometric point
-- statement:
--   Let $R$ be a commutative ring which is an integral domain, let $X$ be a scheme (in the bottom universe) and let $f : X \to \operatorname{Spec} R$ be a morphism which is locally of finite type. Suppose given a point $x$ of $X$ whose image $f(x)$, regarded as a prime ideal of $R$, is the zero ideal, i.e. $x$ lies over the generic point of $\operatorname{Spec} R$. Let $K$ be an algebraically closed field and let $\varphi : R \to K$ be an injective ring homomorphism. The conclusion is that there exists a morphism of schemes $\sigma : \operatorname{Spec} K \to X$ with $\sigma$ followed by $f$ equal to $\operatorname{Spec}(\varphi) : \operatorname{Spec} K \to \operatorname{Spec} R$; that is, $X$ has a $K$-point over the given embedding of $R$ into $K$. No flatness, separatedness or finiteness hypothesis beyond local finiteness of type is imposed, and the point $\sigma$ is not asserted to be related to $x$ beyond the existence claim.
--
--   This is the standard statement that a scheme locally of finite type over a domain whose generic fibre is non-empty acquires a point with values in any algebraically closed field containing the domain (a form of the spreading-out/Nullstellensatz argument of EGA IV 1.10). It is used in the construction of points of a fake elliptic curve over an algebraic closure of $\mathbb{Q}$, via [`CerednikDrinfeld.QM.FakeEllipticCurve.nonempty_algebraicClosure_rat_of_five_le`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.nonempty_algebraicClosure_rat_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_comp_eq_specMap_of_asIdeal_eq_bot_of_locallyOfFiniteType_of_isAlgClosed_of_injective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_comp_eq_specMap_of_asIdeal_eq_bot_of_locallyOfFiniteType_of_isAlgClosed_of_injective
    (R : Type) [CommRing R] [IsDomain R]
    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    (x : X) (hx : (f.base x).asIdeal = ⊥)
    (K : Type) [Field K] [IsAlgClosed K] (φ : R →+* K) (hφ : Function.Injective φ) :
    ∃ σ : Spec (CommRingCat.of K) ⟶ X, σ ≫ f = Spec.map (CommRingCat.ofHom φ) := by sorry
