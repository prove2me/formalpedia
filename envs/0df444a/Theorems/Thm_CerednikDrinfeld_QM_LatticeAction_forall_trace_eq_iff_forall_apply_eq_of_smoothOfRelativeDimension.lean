-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_LatticeAction_forall_trace_eq_iff_forall_apply_eq_of_smoothOfRelativeDimension
-- name    : CerednikDrinfeld.QM.LatticeAction.forall_trace_eq_iff_forall_apply_eq_of_smoothOfRelativeDimension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/737b242f-8517-5854-b476-5c6c9af47c3c
-- title:
--   Trace condition for a lattice action via a trace function
-- statement:
--   Fix rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a commutative ring $R'$, a scheme $A'$ and a morphism $f' : A' \to \operatorname{Spec} R'$ carrying a relative group law $L'$ (functorial multiplication, unit and inverse on the sets $\{\varphi : T \to A' \mid \varphi \text{ followed by } f' = t\}$ of $T$-points over $\operatorname{Spec} R'$, with the group axioms and compatibility with base change), a natural number $d$ with $0 < d$ such that $f'$ is smooth of relative dimension $d$, and a `LatticeAction` $i'$ of $\Lambda$ on $f'$ for $L'$, i.e. endomorphisms $i'.\mathrm{act}\,x$ of $A'$ over $\operatorname{Spec} R'$ that are $L'$-homomorphisms on points, send $1$ to the identity, are multiplicative (contravariantly) and additive for $L'$. Let $k$ be an algebraically closed field, $sk : R' \to k$ a ring homomorphism and $t : \Lambda \to R'$ a function. Call $(V,\tau)$ a presentation of the tangent space when $V$ is a finite-dimensional $k$-vector space and $\tau : V \to \{\varphi : \operatorname{Spec} k[\varepsilon] \to A'\}$ over the tangent base point $\operatorname{Spec} k[\varepsilon] \to \operatorname{Spec} R'$ induced by $sk$ is injective, has image exactly the $P$ with $\operatorname{tangentZero}$ followed by $P$ equal to the unit section at the geometric point $\operatorname{Spec} k \to \operatorname{Spec} R'$, is additive for $L'.\mathrm{mul}$, and satisfies $\tau(c\cdot v) = \operatorname{tangentScale} k\,c$ followed by $\tau(v)$. The hypothesis $ht$ states that for each $x \in \Lambda$, each presentation $(V,\tau)$ and each $k$-linear $\Phi : V \to V$ with $\tau(\Phi v) = \tau(v)$ followed by $i'.\mathrm{act}\,x$ for all $v$, one has $\operatorname{tr}\Phi = sk(t\,x)$. The conclusion is the equivalence: the assertion that for every presentation $(V,\tau)$, every $x \in \Lambda$, every such $\Phi$ for $x$ and every integer $n$ with $x + \bar{x} = n$ in $\mathbb{H}[\mathbb{Q},a,b]$ one has $\operatorname{tr}\Phi = n$ in $k$, holds if and only if $sk(t\,x) = n$ in $k$ for all $x \in \Lambda$ and all integers $n$ with $x + \bar{x} = n$.
--
--   This is the reduction of Drinfeld's trace condition on a quaternionic lattice action, imposed at a geometric point of the base, to a numerical condition on a single trace function $t : \Lambda \to R'$: the reduced quaternion trace of $x$ must be matched by $sk(t\,x)$. It feeds the verification of the trace condition for fake elliptic curves, being cited by [`CerednikDrinfeld.QM.FakeEllipticCurve.trace_eq_of_tower_of_forall_isPullback_of_isCommutative_of_smoothOfRelativeDimension`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.trace_eq_of_tower_of_forall_isPullback_of_isCommutative_of_smoothOfRelativeDimension).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_LatticeAction_forall_trace_eq_iff_forall_apply_eq_of_smoothOfRelativeDimension.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMLatticeAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.LatticeAction.forall_trace_eq_iff_forall_apply_eq_of_smoothOfRelativeDimension
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    {R' : Type} [CommRing R'] {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')} (L' : RelativeGroupLaw R' f')
    (d : ℕ) (hd : 0 < d) [SmoothOfRelativeDimension d f'] (i' : LatticeAction Λ f' L')
    (k : Type) [Field k] [IsAlgClosed k] (sk : R' →+* k) (t : ↥Λ → R')
    (ht : ∀ (x : ↥Λ) (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V]
        (τ : V → SchemeHomOver (tangentBase k sk) f'),
        Function.Injective τ →
        (∀ P : SchemeHomOver (tangentBase k sk) f', P ∈ Set.range τ ↔ IsTangentVector L' k sk P) →
        (∀ v w : V, τ (v + w) = L'.mul (tangentBase k sk) (τ v) (τ w)) →
        (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
        ∀ Φ : V →ₗ[k] V, (∀ v : V, τ (Φ v) = pushPt (i'.act x) (i'.act_over x) (τ v)) →
          LinearMap.trace k V Φ = sk (t x)) :
    (∀ (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) f'),
        Function.Injective τ →
        (∀ P : SchemeHomOver (tangentBase k sk) f', P ∈ Set.range τ ↔ IsTangentVector L' k sk P) →
        (∀ v w : V, τ (v + w) = L'.mul (tangentBase k sk) (τ v) (τ w)) →
        (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
        ∀ (x : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (i'.act x) (i'.act_over x) (τ v)) →
        ∀ n : ℤ, (x : ℍ[ℚ, a, b]) + Star.star (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
          LinearMap.trace k V Φ = (n : k)) ↔
      ∀ (x : ↥Λ) (n : ℤ), (x : ℍ[ℚ, a, b]) + Star.star (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) → sk (t x) = (n : k) := by sorry
