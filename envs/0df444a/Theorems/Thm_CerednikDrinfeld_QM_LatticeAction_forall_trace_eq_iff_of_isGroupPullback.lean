-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_LatticeAction_forall_trace_eq_iff_of_isGroupPullback
-- name    : CerednikDrinfeld.QM.LatticeAction.forall_trace_eq_iff_of_isGroupPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/c5f65559-d7e8-52b9-a2d8-b8fd4faa5202
-- title:
--   Trace condition transports along a group pullback
-- statement:
--   Fix rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a homomorphism $\psi : R' \to R''$ of commutative rings, and schemes $A', A''$ with structure morphisms $f' : A' \to \operatorname{Spec} R'$ and $f'' : A'' \to \operatorname{Spec} R''$ carrying relative group laws $L'$, $L''$ (functorial group structures on the sets of $T$-points over the base, natural in $T$). Let $h : A'' \to A'$ satisfy `IsGroupPullback` for $\psi$: the square formed by $h$, $f''$, $f'$ and $\operatorname{Spec}(\psi)$ is cartesian, and composition with $h$ carries $L''$-products of $T$-points to $L'$-products. Let $i'$, $i''$ be `LatticeAction`s of $\Lambda$ on $(f',L')$ and $(f'',L'')$, i.e. families of endomorphisms over the base that are additive and multiplicative in the lattice variable and additive for the group law on points, and assume they are intertwined by $h$, that is $i''.\mathrm{act}\,x$ followed by $h$ equals $h$ followed by $i'.\mathrm{act}\,x$ for all $x \in \Lambda$. Let $k$ be a field and $sk : R'' \to k$ a ring homomorphism. Then the following two conditions are equivalent. The first: for every finite-dimensional $k$-vector space $V$ and every map $\tau$ from $V$ to the $\operatorname{Spec} k[\varepsilon]$-points of $A''$ over the base point determined by $sk$, such that $\tau$ is injective, its range is exactly the points $P$ with $\mathrm{tangentZero}$ followed by $P$ equal to the unit point over the $k$-point of $sk$, $\tau(v+w) = L''.\mathrm{mul}(\tau v, \tau w)$, and the morphism underlying $\tau(c\cdot v)$ is $\mathrm{tangentScale}\,c$ followed by that of $\tau v$, one has: for every $x \in \Lambda$, every $k$-linear $\Phi : V \to V$ with $\tau(\Phi v)$ equal to $\tau v$ followed by $i''.\mathrm{act}\,x$, and every integer $n$ with $x + \bar x = n$ in $\mathbb{H}[\mathbb{Q},a,b]$, the trace of $\Phi$ equals the image of $n$ in $k$. The second is the same condition for $f'$, $L'$, $i'$ with $sk$ replaced by $sk \circ \psi$.
--
--   This is the transport of Drinfeld's trace condition on a lattice action — that the trace of the differential of the action of $x$ on the tangent space at the origin is the reduced trace of $x$ — between two models linked by a cartesian square of relative group laws, so that the condition may be tested on any model with the same classifying point. It is used in the proof that the locus where the trace condition holds is open and closed, [`AlgebraicGeometry.PolarisedAbelianScheme.exists_opens_isClosed_range_subset_iff_trace`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_opens_isClosed_range_subset_iff_trace).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_LatticeAction_forall_trace_eq_iff_of_isGroupPullback.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMLatticeAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.LatticeAction.forall_trace_eq_iff_of_isGroupPullback
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    {R' R'' : Type} [CommRing R'] [CommRing R''] (ψ : R' →+* R'')
    {A' A'' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')} {f'' : A'' ⟶ Spec (CommRingCat.of R'')}
    (L' : RelativeGroupLaw R' f') (L'' : RelativeGroupLaw R'' f'') (h : A'' ⟶ A')
    (hh : IsGroupPullback ψ L' L'' h) (i' : LatticeAction Λ f' L') (i'' : LatticeAction Λ f'' L'')
    (hact : ∀ x : ↥Λ, i''.act x ≫ h = h ≫ i'.act x)
    (k : Type) [Field k] (sk : R'' →+* k) :
    (∀ (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) f''),
        Function.Injective τ →
        (∀ P : SchemeHomOver (tangentBase k sk) f'', P ∈ Set.range τ ↔ IsTangentVector L'' k sk P) →
        (∀ v w : V, τ (v + w) = L''.mul (tangentBase k sk) (τ v) (τ w)) →
        (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
        ∀ (x : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (i''.act x) (i''.act_over x) (τ v)) →
        ∀ n : ℤ, (x : ℍ[ℚ, a, b]) + Star.star (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
          LinearMap.trace k V Φ = (n : k)) ↔
    (∀ (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V]
        (τ : V → SchemeHomOver (tangentBase k (sk.comp ψ)) f'),
        Function.Injective τ →
        (∀ P : SchemeHomOver (tangentBase k (sk.comp ψ)) f', P ∈ Set.range τ ↔ IsTangentVector L' k (sk.comp ψ) P) →
        (∀ v w : V, τ (v + w) = L'.mul (tangentBase k (sk.comp ψ)) (τ v) (τ w)) →
        (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
        ∀ (x : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (i'.act x) (i'.act_over x) (τ v)) →
        ∀ n : ℤ, (x : ℍ[ℚ, a, b]) + Star.star (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
          LinearMap.trace k V Φ = (n : k)) := by sorry
