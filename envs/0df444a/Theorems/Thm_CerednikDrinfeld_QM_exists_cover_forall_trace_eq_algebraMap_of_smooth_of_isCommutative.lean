-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_cover_forall_trace_eq_algebraMap_of_smooth_of_isCommutative
-- name    : CerednikDrinfeld.QM.exists_cover_forall_trace_eq_algebraMap_of_smooth_of_isCommutative
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/7724bb0a-4b40-596b-8af9-46001d367042
-- title:
--   Zariski-local trace function for a quaternionic action
-- statement:
--   Fix rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a commutative ring $R$, a scheme $A$ and a morphism $f : A \to \operatorname{Spec} R$. Let $L$ be a relative group law for $f$, i.e. a group structure on the sets $\{\varphi : T \to A \mid \varphi \text{ followed by } f = t\}$ of sections over each base morphism $t : T \to \operatorname{Spec} R$, natural under precomposition in $T$; assume $L$ is commutative, $f$ is smooth, and that $\Lambda$ acts by endomorphisms $\mathrm{act}\,x : A \to A$ with $\mathrm{act}\,x$ followed by $f$ equal to $f$, each acting on sections (by $P \mapsto P$ followed by $\mathrm{act}\,x$) as a homomorphism for $L.\mathrm{mul}$ over every base. Then there are finitely many $c_0,\dots,c_{n-1} \in R$ generating the unit ideal such that for each $i$ and each $R$-algebra $R_i$ that is a localisation of $R$ away from $c_i$ there is a function $t : \Lambda \to R_i$ with the following property. Let $k$ be a field that is an $R_i$-algebra and $s_k : R \to k$ the resulting composite structure map, and let $x \in \Lambda$. Let $V$ be a $k$-vector space and $\tau : V \to \{$sections of $f$ over $\operatorname{Spec} k[\varepsilon] \to \operatorname{Spec} R$ induced by $s_k\}$ an injection whose image is exactly the set of tangent vectors at the origin (those sections $P$ with $P$ precomposed with the closed immersion $\operatorname{Spec} k \to \operatorname{Spec} k[\varepsilon]$ equal to the identity section $L.\mathrm{one}$ over $\operatorname{Spec} k \to \operatorname{Spec} R$), carrying addition to $L.\mathrm{mul}$ and scalar multiplication by $c \in k$ to precomposition with the scaling $\varepsilon \mapsto c\varepsilon$ of $\operatorname{Spec} k[\varepsilon]$. Then every $k$-linear endomorphism $\Phi$ of $V$ inducing the action of $\mathrm{act}\,x$ on tangent vectors through $\tau$ satisfies $\operatorname{tr}_k \Phi =$ the image of $t(x)$ under $R_i \to k$.
--
--   This is the Zariski-local form of the statement that the trace of the differential of the $\Lambda$-action at the origin of a smooth commutative relative group scheme is the specialisation of an element of the base ring, independent of the chosen geometric point and of the chosen presentation of the tangent space. It is obtained from the local description of the formal group along the identity of a smooth commutative relative group law, and is used to compare traces at different points of the base in the quaternionic-moduli part of the Čerednik–Drinfeld material.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_cover_forall_trace_eq_algebraMap_of_smooth_of_isCommutative.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.exists_cover_forall_trace_eq_algebraMap_of_smooth_of_isCommutative
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hL : L.IsCommutative) (hf : Smooth f)
    (act : ↥Λ → (A ⟶ A)) (act_over : ∀ x : ↥Λ, act x ≫ f = f)
    (act_hom : ∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      pushPt (act x) (act_over x) (L.mul t P Q) = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q)) :
    ∃ (n : ℕ) (c : Fin n → R), Ideal.span (Set.range c) = ⊤ ∧
      ∀ (i : Fin n) (Rᵢ : Type u) [CommRing Rᵢ] [Algebra R Rᵢ] [IsLocalization.Away (c i) Rᵢ],
        ∃ t : ↥Λ → Rᵢ,
          ∀ (k : Type u) [Field k] [Algebra Rᵢ k] (sk : R →+* k),
            (algebraMap Rᵢ k).comp (algebraMap R Rᵢ) = sk →
            ∀ (x : ↥Λ) (V : Type u) [AddCommGroup V] [Module k V] (τ : V → SchemeHomOver (tangentBase k sk) f),
              Function.Injective τ →
              (∀ P : SchemeHomOver (tangentBase k sk) f, P ∈ Set.range τ ↔ IsTangentVector L k sk P) →
              (∀ v w : V, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w)) →
              (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
              ∀ Φ : V →ₗ[k] V, (∀ v : V, τ (Φ v) = pushPt (act x) (act_over x) (τ v)) →
                LinearMap.trace k V Φ = algebraMap Rᵢ k (t x) := by sorry
