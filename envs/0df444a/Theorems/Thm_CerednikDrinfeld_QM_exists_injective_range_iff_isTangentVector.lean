-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_injective_range_iff_isTangentVector
-- name    : CerednikDrinfeld.QM.exists_injective_range_iff_isTangentVector
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/779bfde6-e984-5e29-a73c-db49aa84fea8
-- title:
--   A linear presentation of tangent vectors at the origin
-- statement:
--   Let $B$ be a commutative ring, let $A$ be a scheme (in universe $0$) and let $f\colon A\to\operatorname{Spec}B$ be a morphism equipped with a relative group law $L$: that is, for every scheme $T$ and every $t\colon T\to\operatorname{Spec}B$ a multiplication, unit and inverse on the set $\{\varphi\colon T\to A \mid \varphi\ \text{followed by}\ f = t\}$ of $T$-points of $A$ over $B$, satisfying associativity, the unit laws and left inverse law, and compatible with base change along any $\psi\colon T'\to T$ with $\psi$ followed by $t$ equal to $t'$. Let $k$ be a field and $sk\colon B\to k$ a ring homomorphism. The assertion is the existence of a type $V$, an additive commutative group structure and a $k$-module structure on $V$, and a map $\tau$ from $V$ to the points of $A$ over $B$ with base $\operatorname{Spec}$ of the composite $B\to k\to k[\varepsilon]$ (morphisms $\operatorname{Spec}k[\varepsilon]\to A$ whose composite with $f$ is that base morphism), such that: $\tau$ is injective; a point $P$ lies in the range of $\tau$ if and only if restricting $P$ along $\varepsilon\mapsto 0$, i.e. the morphism $\operatorname{Spec}(k[\varepsilon]\to k)$ followed by $P$, equals the unit point of $L$ over $\operatorname{Spec}(sk)\colon\operatorname{Spec}k\to\operatorname{Spec}B$; $\tau(v+w)=L.\mathrm{mul}(\tau v,\tau w)$ for all $v,w$; and for $c\in k$ and $v\in V$ the underlying morphism of $\tau(c\cdot v)$ is $\operatorname{Spec}$ of the map of dual numbers induced by $c\cdot\mathrm{id}_k$ followed by the underlying morphism of $\tau v$.
--
--   This is the statement that the tangent vectors at the origin of the fibre at $sk$ of a scheme with a relative group law carry the structure of a $k$-vector space, with addition given by the group law and scalar multiplication by the scalings $\varepsilon\mapsto c\varepsilon$ of the dual numbers: the Lie algebra of the fibre, presented as a pair $(V,\tau)$. The existence of such a presentation is what the tangent-space and trace statements for polarised abelian schemes and for the moduli of fake elliptic curves quantify over.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_injective_range_iff_isTangentVector.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.exists_injective_range_iff_isTangentVector
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)
    (k : Type) [Field k] (sk : B →+* k) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module k V) (τ : V → SchemeHomOver (tangentBase k sk) f),
      Function.Injective τ ∧
      (∀ P, P ∈ Set.range τ ↔ IsTangentVector L k sk P) ∧
      (∀ v w, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w)) ∧
      (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) := by sorry
