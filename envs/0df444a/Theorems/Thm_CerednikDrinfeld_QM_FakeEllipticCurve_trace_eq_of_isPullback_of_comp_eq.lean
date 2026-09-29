-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_trace_eq_of_isPullback_of_comp_eq
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.trace_eq_of_isPullback_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/5a8dfe2d-e111-5f50-9c0b-c8742c13f7eb
-- title:
--   Trace condition descends along a cartesian square
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, commutative rings $S,S'$ and a ring homomorphism $\varphi : S \to S'$, together with a fake elliptic curve $E_0$ of type $(\Lambda,N)$ over $S'$. On the side of $S$, let $f : \mathcal{A} \to \operatorname{Spec} S$ be a scheme over $\operatorname{Spec} S$ carrying a relative group law $L$ (a functorial group structure on the sets $\{\phi : T \to \mathcal{A} \mid \phi \circ f = t\}$ of points over each base morphism $t$, natural in $T$), and let $\mathrm{act} : \Lambda \to \operatorname{End}(\mathcal{A})$ satisfy $\mathrm{act}(x)$ followed by $f$ equals $f$ for all $x$. Assume $g : E_0.A \to \mathcal{A}$ makes the square with $E_0.f$, $f$ and $\operatorname{Spec}\varphi$ cartesian, that $g$ carries the group law of $E_0$ to that of $L$ on points (for every $t' : T \to \operatorname{Spec} S'$ and points $x,y$ over $t'$, the product $E_0.L.\mathrm{mul}\,t'\,x\,y$ followed by $g$ equals the $L$-product over $t'$ followed by $\operatorname{Spec}\varphi$ of the composites $x \cdot g$ and $y \cdot g$), and that $E_0.\mathrm{act}(x)$ followed by $g$ equals $g$ followed by $\mathrm{act}(x)$ for every $x \in \Lambda$. Let $k$ be an algebraically closed field and $sk : S \to k$, $s : S' \to k$ ring homomorphisms with $s \circ \varphi = sk$. The conclusion is the trace condition for $(\mathcal{A},f,L,\mathrm{act})$ at $sk$: for every finite-dimensional $k$-vector space $V$ and every injective $\tau$ from $V$ to the points of $f$ over the base morphism $\operatorname{Spec} k[\varepsilon] \to \operatorname{Spec} S$ induced by $sk$, whose range is exactly the set of $P$ with $\mathrm{tangentZero}$ followed by $P$ equal to the identity section over the geometric point $sk$, which is additive for $L.\mathrm{mul}$ and satisfies $\tau(c \cdot v) = \mathrm{tangentScale}(c)$ followed by $\tau(v)$, and for every $m \in \Lambda$, every $k$-linear $\Phi : V \to V$ with $\tau(\Phi v)$ equal to $\tau(v)$ followed by $\mathrm{act}(m)$, and every integer $n$ with $m + m^{*} = n$ in $\mathbb{H}[\mathbb{Q},a,b]$, one has $\operatorname{tr}_k(\Phi) = n$ in $k$.
--
--   This is the descent of Drinfeld's trace condition — one of the defining axioms of a fake elliptic curve, relating the trace of the differential of the action of $m \in \Lambda$ on the tangent space at a geometric point to the reduced trace $m + m^{*}$ — from a fake elliptic curve over $S'$ to a group-law-with-action datum over $S$ along a cartesian square of bases. It is used in the construction of fake elliptic curves over a base ring from ones over an extension or quotient, via pullback, pushout along nilpotent surjections, and towers of bases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_trace_eq_of_isPullback_of_comp_eq.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.trace_eq_of_isPullback_of_comp_eq
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    (E₀ : FakeEllipticCurve Λ N S')
    {𝒜 : Scheme.{u}} {f : 𝒜 ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (act : ↥Λ → (𝒜 ⟶ 𝒜)) (act_over : ∀ x : ↥Λ, act x ≫ f = f)
    (g : E₀.A ⟶ 𝒜) (hg : CategoryTheory.IsPullback g E₀.f f (Spec.map (CommRingCat.ofHom φ)))
    (hg_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' E₀.f),
      (E₀.L.mul t' x y).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨x.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1)
    (hg_act : ∀ x : ↥Λ, E₀.act x ≫ g = g ≫ act x)
    (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) (s : S' →+* k) (hs : s.comp φ = sk) :
      ∀ (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) f),
        Function.Injective τ →
        (∀ P : SchemeHomOver (tangentBase k sk) f, P ∈ Set.range τ ↔ IsTangentVector L k sk P) →
        (∀ v w : V, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w)) →
        (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
        ∀ (m : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (act m) (act_over m) (τ v)) →
        ∀ n : ℤ, (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
          LinearMap.trace k V Φ = (n : k) := by sorry
