-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_existsUnique_linearMap_forall_eq_pushPt
-- name    : CerednikDrinfeld.QM.existsUnique_linearMap_forall_eq_pushPt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/e565c7ee-125e-58f2-a669-5a4de1daa406
-- title:
--   Differential at the origin of a homomorphism of points
-- statement:
--   Let $B$ be a commutative ring, $A$ a scheme, $f\colon A\to\operatorname{Spec}B$ a morphism, and $L$ a `RelativeGroupLaw` for $f$: for every test scheme $T$ and every $t\colon T\to\operatorname{Spec}B$ a multiplication, unit and inversion on the set $\{\varphi\colon T\to A\mid \varphi\text{ followed by }f=t\}$ of $t$-points of $A$, satisfying the group axioms and natural in $T$ under precomposition. Let $k$ be a field and $sk\colon B\to k$ a ring homomorphism; write $\mathrm{tangentBase}$ for the morphism $\operatorname{Spec}k[\varepsilon]\to\operatorname{Spec}B$ induced by $B\to k\to k[\varepsilon]$ (dual numbers), $\mathrm{geomPoint}$ for the one induced by $sk$, $\mathrm{tangentZero}$ for the closed immersion induced by $\varepsilon\mapsto 0$, and $\mathrm{tangentScale}\,c$ for the endomorphism of $\operatorname{Spec}k[\varepsilon]$ induced by $\varepsilon\mapsto c\varepsilon$. Let $V$ be a $k$-vector space and $\tau$ a map from $V$ to the $\mathrm{tangentBase}$-points of $A$ such that: $\tau$ is injective; the image of $\tau$ consists exactly of the points $P$ with $\mathrm{tangentZero}$ followed by $P$ equal to the unit $\mathrm{geomPoint}$-point, i.e. the tangent vectors at the origin; $\tau(v+w)=L.\mathrm{mul}(\tau v,\tau w)$; and the morphism underlying $\tau(c\cdot v)$ is $\mathrm{tangentScale}\,c$ followed by that of $\tau(v)$. Let $g\colon A\to A$ satisfy $g$ followed by $f$ equals $f$, and assume that postcomposition with $g$ commutes with $L.\mathrm{mul}$ on $t$-points for every test scheme and every $t$. Then there is a unique $k$-linear map $\Phi\colon V\to V$ with $\tau(\Phi v)=\tau(v)$ followed by $g$, for all $v\in V$.
--
--   This constructs the differential at the origin of an endomorphism of a relative group scheme which is a homomorphism on points, as a $k$-linear endomorphism of the tangent space presented abstractly by the pair $(V,\tau)$. It is the source of the linear map whose trace enters Drinfeld's trace condition, and is used in the statements about traces of lattice actions and of endomorphisms of polarised abelian schemes in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_existsUnique_linearMap_forall_eq_pushPt.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.existsUnique_linearMap_forall_eq_pushPt
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)
    (k : Type) [Field k] (sk : B →+* k)
    (V : Type) [AddCommGroup V] [Module k V] (τ : V → SchemeHomOver (tangentBase k sk) f)
    (hinj : Function.Injective τ)
    (hrange : ∀ P, P ∈ Set.range τ ↔ IsTangentVector L k sk P)
    (hadd : ∀ v w, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w))
    (hsmul : ∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1)
    (g : A ⟶ A) (hg : g ≫ f = f)
    (hg_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t f),
      pushPt g hg (L.mul t P Q) = L.mul t (pushPt g hg P) (pushPt g hg Q)) :
    ∃! Φ : V →ₗ[k] V, ∀ v : V, τ (Φ v) = pushPt g hg (τ v) := by sorry
