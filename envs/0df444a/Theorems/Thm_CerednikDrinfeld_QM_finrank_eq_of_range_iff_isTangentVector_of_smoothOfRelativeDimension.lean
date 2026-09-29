-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension
-- name    : CerednikDrinfeld.QM.finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/acb36559-2942-535e-a86b-9baffe6ac84f
-- title:
--   Tangent space at the origin has dimension n
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f\colon A \to \operatorname{Spec} S$ a morphism carrying an instance of `SmoothOfRelativeDimension n` for a natural number $n$, and let $L$ be a relative group law on $f$, i.e. a rule assigning to every $S$-scheme $t\colon T \to \operatorname{Spec} S$ a group structure (multiplication `L.mul`, unit `L.one`, inverse `L.inv`, with associativity, unit and inverse laws) on the set of morphisms $\varphi\colon T \to A$ with $\varphi$ followed by $f$ equal to $t$, the multiplication being natural in $T$ under precomposition. Let $k$ be a field and $sk\colon S \to k$ a ring homomorphism; write $\operatorname{Spec} k[\varepsilon] \to \operatorname{Spec} S$ for the structure map `tangentBase k sk` induced by $S \to k \to k[\varepsilon]$ and $\operatorname{Spec} k \to \operatorname{Spec} S$ for `geomPoint k sk`. Let $V$ be a $k$-vector space and $\tau$ a map from $V$ to the set of morphisms $\operatorname{Spec} k[\varepsilon] \to A$ over `tangentBase k sk`, subject to: $\tau$ is injective; the image of $\tau$ consists exactly of those points $P$ with $\varepsilon \mapsto 0$ followed by $P$ equal to the unit section $L.\mathrm{one}$ at `geomPoint k sk` (the predicate `IsTangentVector`); $\tau(v+w) = L.\mathrm{mul}(\tau v, \tau w)$ on $k[\varepsilon]$-points; and $\tau(c \cdot v)$ is `tangentScale k c` (induced by $\varepsilon \mapsto c\varepsilon$) followed by $\tau v$, for all $c \in k$. Then $\dim_k V = n$.
--
--   This identifies the tangent space at the origin of the geometric fibre $A_k$, presented abstractly as a $k$-vector space $V$ parametrising the kernel of $A(k[\varepsilon]) \to A(k)$, with an $n$-dimensional space when the structure morphism is smooth of relative dimension $n$. It is used to evaluate Drinfeld-style trace conditions on smooth models (in particular of relative dimension $2$) in the Čerednik–Drinfeld part of the development, being cited by the results on traces of lattice actions and on fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension
    {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (k : Type u) [Field k] (sk : S →+* k)
    (V : Type u) [AddCommGroup V] [Module k V] (τ : V → SchemeHomOver (tangentBase k sk) f)
    (hinj : Function.Injective τ)
    (hrange : ∀ P : SchemeHomOver (tangentBase k sk) f, P ∈ Set.range τ ↔ IsTangentVector L k sk P)
    (hadd : ∀ v w : V, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w))
    (hsmul : ∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) :
    Module.finrank k V = n := by sorry
