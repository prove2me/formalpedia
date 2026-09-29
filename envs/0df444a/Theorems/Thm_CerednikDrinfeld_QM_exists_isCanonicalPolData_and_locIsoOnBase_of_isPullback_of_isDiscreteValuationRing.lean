-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_isCanonicalPolData_and_locIsoOnBase_of_isPullback_of_isDiscreteValuationRing
-- name    : CerednikDrinfeld.QM.exists_isCanonicalPolData_and_locIsoOnBase_of_isPullback_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/5ba1e833-1a00-5e3b-a02f-536761605860
-- title:
--   Canonical cube polarisation datum extends over a discrete valuation ring
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`, i.e. $0 < a$ or $0 < b$, and for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a maximal order (an order, and maximal among orders), $\mu \in \Lambda$ with $\mu^2 = -(qq')\cdot 1$, and $star : \Lambda \to \Lambda$ a map with $\mu \cdot star(x) = \bar{x}\mu$ for all $x \in \Lambda$. Let $\mathcal{O}$ be a discrete valuation domain with fraction field $K$. Over $\mathrm{Spec}\,\mathcal{O}$ let $f : A \to \mathrm{Spec}\,\mathcal{O}$ carry a commutative `RelativeGroupLaw` $L$, satisfy `AbelianSchemePropertyBundle` (smooth, proper, connected fibres, a relative group law exists), have all fibres of topological Krull dimension $2$, and carry an invertible module `pol`; let $f_K, L_K, \mathrm{pol}_K$ be data of the same shape over $K$. Let $g : A_K \to A$ make the square over $\mathrm{Spec}\,K \to \mathrm{Spec}\,\mathcal{O}$ cartesian, be compatible with $L_K$ and $L$ on points over any base, and satisfy $g^{*}\,\mathrm{pol} \cong \mathrm{pol}_K$. Let $\Lambda$ act by endomorphisms $act$ of $A$ over $f$ and $act_K$ of $A_K$ over $f_K$, each acting by homomorphisms on points, sending $1$ to the identity, satisfying $act(xy) = act(y) \mathbin{;} act(x)$ (so $act(x) \circ act(y)$), additive in $x$ on points, and satisfying the trace condition: for every algebraically closed $k$, ring map $s_k$ from the base, finite-dimensional $k$-space $V$ with an injective additive $k$-scaling-compatible parametrisation $\tau$ of exactly the tangent vectors at the identity over the dual-number base, and $k$-linear $\Phi$ with $\tau(\Phi v) = act(x)_{*}\tau(v)$, one has $\mathrm{tr}_k \Phi = n$ whenever $x + \bar{x} = n \in \mathbb{Z}$; and let $act_K(x) \mathbin{;} g = g \mathbin{;} act(x)$. Assume over $K$ there is $\mathcal{L}_{E,K}$ with `IsCanonicalPolData` for $(f_K, L_K, act_K, star)$ — invertible, symmetric and with two-torsion kernel in the sense of the Mumford bundle, admitting a faithfully flat base change on which it becomes $\mathcal{L}_0 \otimes (-1)^{*}\mathcal{L}_0$ with $\mathcal{L}_0$ of trivial kernel, with positive geometric fibre $H^0$-rank at every algebraically closed point, and Rosati-compatible with $act_K$ and $star$ — such that $\mathrm{pol}_K$ and $\mathcal{L}_{E,K}^{\otimes 3}$ are locally isomorphic over the base. Then there exists $\mathcal{L}_E$ on $A$ satisfying `IsCanonicalPolData` for $(f, L, act, star)$ with $\mathrm{pol}$ and $\mathcal{L}_E^{\otimes 3}$ locally isomorphic over $\mathrm{Spec}\,\mathcal{O}$. Here $star$ enters only as the index involution in the Rosati compatibility clause.
--
--   This is the polarisation clause in the valuative extension step for quaternionic (fake elliptic curve) data: a canonical cube polarisation datum on the generic fibre of an abelian scheme over a discrete valuation ring, compatible with the action of a maximal order, descends to the whole scheme. It is phrased directly on schemes, group laws, modules and actions rather than on the packaged records, and is used in the assembly of [`AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_isPullback_algebraMap_of_isDiscreteValuationRing`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_isPullback_algebraMap_of_isDiscreteValuationRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_isCanonicalPolData_and_locIsoOnBase_of_isPullback_of_isDiscreteValuationRing.lean

import Definitions.Def_CerednikDrinfeld_QMCanonicalPol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation CerednikDrinfeld CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.exists_isCanonicalPolData_and_locIsoOnBase_of_isPullback_of_isDiscreteValuationRing
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (K : Type) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of 𝒪)) (L : RelativeGroupLaw 𝒪 f) (hL : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle 𝒪 f)
    (hdim : ∀ s : ↥(Spec (CommRingCat.of 𝒪)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = 2)
    (pol : A.Modules) (hpol : Scheme.Modules.IsInvertible pol)
    {AK : Scheme.{0}} (fK : AK ⟶ Spec (CommRingCat.of K)) (LK : RelativeGroupLaw K fK) (hLK : LK.IsCommutative)
    (hAK : AbelianSchemePropertyBundle K fK)
    (hdimK : ∀ s : ↥(Spec (CommRingCat.of K)), topologicalKrullDim ↥(fK.base ⁻¹' {s}) = 2)
    (polK : AK.Modules) (hpolK : Scheme.Modules.IsInvertible polK)
    (g : AK ⟶ A) (hg : CategoryTheory.IsPullback g fK f (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 K))))
    (hg_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t' fK),
      (LK.mul t' x y).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 K)))
          ⟨x.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1)
    (hg_pol : Nonempty ((Scheme.Modules.pullback g).obj pol ≅ polK))
    (act : ↥Λ → (A ⟶ A)) (act_over : ∀ x : ↥Λ, act x ≫ f = f)
    (act_hom : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of 𝒪)) (P Q : SchemeHomOver t f),
      pushPt (act x) (act_over x) (L.mul t P Q) =
        L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q))
    (act_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 A)
    (act_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x)
    (act_add : ∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of 𝒪)) (P : SchemeHomOver t f),
      pushPt (act (x + y)) (act_over (x + y)) P =
        L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P))
    (act_trace : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : 𝒪 →+* k)
      (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) f),
      Function.Injective τ →
      (∀ P : SchemeHomOver (tangentBase k sk) f, P ∈ Set.range τ ↔ IsTangentVector L k sk P) →
      (∀ v w : V, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w)) →
      (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
      ∀ (x : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (act x) (act_over x) (τ v)) →
      ∀ n : ℤ, (x : ℍ[ℚ, a, b]) + Star.star (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
        LinearMap.trace k V Φ = (n : k))
    (actK : ↥Λ → (AK ⟶ AK)) (actK_over : ∀ x : ↥Λ, actK x ≫ fK = fK)
    (actK_hom : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t fK),
      pushPt (actK x) (actK_over x) (LK.mul t P Q) =
        LK.mul t (pushPt (actK x) (actK_over x) P) (pushPt (actK x) (actK_over x) Q))
    (actK_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, actK ⟨1, h⟩ = 𝟙 AK)
    (actK_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      actK ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = actK y ≫ actK x)
    (actK_add : ∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver t fK),
      pushPt (actK (x + y)) (actK_over (x + y)) P =
        LK.mul t (pushPt (actK x) (actK_over x) P) (pushPt (actK y) (actK_over y) P))
    (actK_trace : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : K →+* k)
      (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) fK),
      Function.Injective τ →
      (∀ P : SchemeHomOver (tangentBase k sk) fK, P ∈ Set.range τ ↔ IsTangentVector LK k sk P) →
      (∀ v w : V, τ (v + w) = LK.mul (tangentBase k sk) (τ v) (τ w)) →
      (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
      ∀ (x : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (actK x) (actK_over x) (τ v)) →
      ∀ n : ℤ, (x : ℍ[ℚ, a, b]) + Star.star (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
        LinearMap.trace k V Φ = (n : k))
    (hg_act : ∀ x : ↥Λ, actK x ≫ g = g ≫ act x)
    (hK : ∃ polEK : AK.Modules, IsCanonicalPolData fK LK actK actK_over star polEK ∧
      LocIsoOnBase fK polK (polEK ⊗ polEK ⊗ polEK)) :
    ∃ polE : A.Modules, IsCanonicalPolData f L act act_over star polE ∧
      LocIsoOnBase f pol (polE ⊗ polE ⊗ polE) := by sorry
