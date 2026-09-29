-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_trace_eq_of_isPullback_algebraMap_of_injective
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.trace_eq_of_isPullback_algebraMap_of_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/168df7be-b8e0-5f29-914d-33ba67faa09d
-- title:
--   Trace condition for an integral model at injective geometric points
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, a commutative ring $R$ and a field $K$ which is a fraction field of $R$, and let $E_0$ be a fake elliptic curve of type $(\Lambda,N)$ over $K$. Let $f : \mathcal{A} \to \operatorname{Spec} R$ be a scheme over $R$ equipped with a relative group law $L$ (functorial multiplication, unit, inverse on $T$-points over $\operatorname{Spec} R$, with associativity, unit, inverse and base-change naturality), and with morphisms $\mathrm{act}(x) : \mathcal{A} \to \mathcal{A}$ over $\operatorname{Spec} R$ for $x \in \Lambda$. Assume given $g : E_0.A \to \mathcal{A}$ making the square formed by $g$, $E_0.f$, $f$ and $\operatorname{Spec}$ of the structure map $R \to K$ cartesian, such that $g$ is compatible with the two group laws on $T$-points over any $t' : T \to \operatorname{Spec} K$, and such that $E_0.\mathrm{act}(x)$ followed by $g$ equals $g$ followed by $\mathrm{act}(x)$ for all $x \in \Lambda$. The conclusion is the trace clause for $(\mathcal{A},f,L,\mathrm{act})$ at every injective geometric point: for every algebraically closed field $k$ and every injective ring homomorphism $s_k : R \to k$, every finite-dimensional $k$-vector space $V$ and every injective map $\tau$ from $V$ to the set of morphisms $\operatorname{Spec} k[\varepsilon] \to \mathcal{A}$ lying over $\operatorname{Spec}$ of $k \to k[\varepsilon]$ composed with $s_k$, whose image consists exactly of those points $P$ with $\mathrm{tangentZero}$ followed by $P$ equal to the unit of $L$ at the geometric point of $s_k$, which takes addition in $V$ to multiplication in $L$ and scalar multiplication by $c \in k$ to precomposition with $\mathrm{tangentScale}\,k\,c$: for all $m \in \Lambda$ and all $k$-linear $\Phi : V \to V$ with $\tau(\Phi v)$ equal to $\tau(v)$ followed by $\mathrm{act}(m)$, and every integer $n$ with $m + \bar m = n$ in $\mathbb{H}[\mathbb{Q},a,b]$, one has $\operatorname{tr}_k(\Phi) = n$ in $k$.
--
--   This is Drinfeld's trace condition on the differential of the $\Lambda$-action, transported from the generic fibre $E_0$ to an integral model $\mathcal{A}$ along the cartesian square, and it is weaker than the corresponding `act_trace` clause of `FakeEllipticCurve` in that it is asserted only at geometric points $s_k : R \to k$ that are injective, i.e. factor through the generic point. It is used in the construction of a fake elliptic curve over $R$ pulling back to a given one over $K$ ([`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_algebraMap_of_abelianSchemePropertyBundle_of_isPullback`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_algebraMap_of_abelianSchemePropertyBundle_of_isPullback)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_trace_eq_of_isPullback_algebraMap_of_injective.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.trace_eq_of_isPullback_algebraMap_of_injective
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {R K : Type u} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (E₀ : FakeEllipticCurve Λ N K)
    {𝒜 : Scheme.{u}} {f : 𝒜 ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (act : ↥Λ → (𝒜 ⟶ 𝒜)) (act_over : ∀ x : ↥Λ, act x ≫ f = f)
    (g : E₀.A ⟶ 𝒜) (hg : CategoryTheory.IsPullback g E₀.f f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hg_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t' E₀.f),
      (E₀.L.mul t' x y).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨x.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1)
    (hg_act : ∀ x : ↥Λ, E₀.act x ≫ g = g ≫ act x) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : R →+* k), Function.Injective sk →
      ∀ (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) f),
        Function.Injective τ →
        (∀ P : SchemeHomOver (tangentBase k sk) f, P ∈ Set.range τ ↔ IsTangentVector L k sk P) →
        (∀ v w : V, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w)) →
        (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
        ∀ (m : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (act m) (act_over m) (τ v)) →
        ∀ n : ℤ, (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
          LinearMap.trace k V Φ = (n : k) := by sorry
