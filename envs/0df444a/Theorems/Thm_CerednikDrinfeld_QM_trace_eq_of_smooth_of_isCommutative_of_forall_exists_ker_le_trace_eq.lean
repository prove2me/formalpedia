-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_trace_eq_of_smooth_of_isCommutative_of_forall_exists_ker_le_trace_eq
-- name    : CerednikDrinfeld.QM.trace_eq_of_smooth_of_isCommutative_of_forall_exists_ker_le_trace_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/9dff6ae7-85b7-5458-ad02-6fbc99bbdc17
-- title:
--   Drinfeld's trace condition descends from generising geometric points
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a commutative ring $R$, a scheme $\mathcal{A}$ and a morphism $f : \mathcal{A} \to \operatorname{Spec} R$. Let $L$ be a relative group law for $f$, i.e. a group structure on the sections $\{\varphi : T \to \mathcal{A} \mid \varphi \text{ followed by } f = t\}$ for every $t : T \to \operatorname{Spec} R$, natural under base change, assumed commutative ($L$'s multiplication is symmetric on all such $T$), and let $f$ be smooth. Let $\mathrm{act}$ assign to each $x \in \Lambda$ an endomorphism $\mathrm{act}\,x$ of $\mathcal{A}$ over $\operatorname{Spec} R$ (composing with $f$ gives back $f$) such that post-composition with $\mathrm{act}\,x$ is a homomorphism for $L$ on sections over any base. The hypothesis is that for every algebraically closed field $k$ and ring homomorphism $s_k : R \to k$ there are an algebraically closed field $k_0$ and $s_0 : R \to k_0$ with $\ker s_0 \subseteq \ker s_k$ at which the following trace condition holds: whenever $V$ is a finite-dimensional $k_0$-vector space and $\tau : V \to \{P : \operatorname{Spec} k_0[\varepsilon] \to \mathcal{A}$ over $\operatorname{Spec} R$ via $s_0\}$ is injective, has image exactly the tangent vectors (those $P$ whose restriction along $k_0[\varepsilon] \to k_0$ is the unit section at the geometric point $s_0$), is additive for $L$'s multiplication, and satisfies $\tau(c \cdot v) = \mathrm{tangentScale}\,c$ followed by $\tau(v)$ for $c \in k_0$, then for every $m \in \Lambda$, every $k_0$-linear $\Phi : V \to V$ with $\tau(\Phi v) = \tau(v)$ followed by $\mathrm{act}\,m$, and every integer $n$ with $m + \bar m = n$ in $\mathbb{H}[\mathbb{Q},a,b]$, one has $\operatorname{tr} \Phi = n$ in $k_0$. The conclusion is that this same trace condition holds at every algebraically closed field $k$ and every $s_k : R \to k$.
--
--   This is the spreading-out step for Drinfeld's trace condition in the theory of fake elliptic curves with quaternionic multiplication: the condition $\operatorname{tr}(d\,\mathrm{act}(m)) = m + \bar m$ on tangent spaces need only be checked at one generising geometric point above each point of $\operatorname{Spec} R$. It is used in verifying the trace condition after descent along a pullback square, via the existence of a formal group along the unit section of a smooth commutative relative group law.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_trace_eq_of_smooth_of_isCommutative_of_forall_exists_ker_le_trace_eq.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.trace_eq_of_smooth_of_isCommutative_of_forall_exists_ker_le_trace_eq
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    {R : Type u} [CommRing R]
    {𝒜 : Scheme.{u}} {f : 𝒜 ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (hL : L.IsCommutative) (hf : Smooth f)
    (act : ↥Λ → (𝒜 ⟶ 𝒜)) (act_over : ∀ x : ↥Λ, act x ≫ f = f)
    (act_hom : ∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      pushPt (act x) (act_over x) (L.mul t P Q) = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q))
    (hgen : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : R →+* k),
      ∃ (k₀ : Type u) (_ : Field k₀) (_ : IsAlgClosed k₀) (s₀ : R →+* k₀), RingHom.ker s₀ ≤ RingHom.ker sk ∧
      ∀ (V : Type u) [AddCommGroup V] [Module k₀ V] [Module.Finite k₀ V] (τ : V → SchemeHomOver (tangentBase k₀ s₀) f),
        Function.Injective τ →
        (∀ P : SchemeHomOver (tangentBase k₀ s₀) f, P ∈ Set.range τ ↔ IsTangentVector L k₀ s₀ P) →
        (∀ v w : V, τ (v + w) = L.mul (tangentBase k₀ s₀) (τ v) (τ w)) →
        (∀ (c : k₀) (v : V), (τ (c • v)).1 = tangentScale k₀ c ≫ (τ v).1) →
        ∀ (m : ↥Λ) (Φ : V →ₗ[k₀] V), (∀ v : V, τ (Φ v) = pushPt (act m) (act_over m) (τ v)) →
        ∀ n : ℤ, (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
          LinearMap.trace k₀ V Φ = (n : k₀)) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : R →+* k),
      ∀ (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) f),
        Function.Injective τ →
        (∀ P : SchemeHomOver (tangentBase k sk) f, P ∈ Set.range τ ↔ IsTangentVector L k sk P) →
        (∀ v w : V, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w)) →
        (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
        ∀ (m : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (act m) (act_over m) (τ v)) →
        ∀ n : ℤ, (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
          LinearMap.trace k V Φ = (n : k) := by sorry
