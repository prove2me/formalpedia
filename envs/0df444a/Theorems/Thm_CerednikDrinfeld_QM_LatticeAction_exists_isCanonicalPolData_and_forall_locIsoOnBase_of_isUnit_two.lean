-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_LatticeAction_exists_isCanonicalPolData_and_forall_locIsoOnBase_of_isUnit_two
-- name    : CerednikDrinfeld.QM.LatticeAction.exists_isCanonicalPolData_and_forall_locIsoOnBase_of_isUnit_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/44d25392-4754-5319-8f79-a13fa6f61fc4
-- title:
--   Canonical polarisation datum for a quaternionic action on an abelian surface
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is an order maximal among orders, let $\mu \in \Lambda$ satisfy $\mu^2 = -(qq')\cdot 1$, and let $\mathrm{star} : \Lambda \to \Lambda$ satisfy $\mu \cdot \mathrm{star}(x) = \bar{x}\mu$ for all $x \in \Lambda$. Let $S$ be a commutative ring in which $2$ is a unit, $f : A \to \operatorname{Spec} S$ a morphism of schemes, $L$ a commutative relative group law on $f$ (functorial multiplication, unit and inverse on $S$-points, compatible with base change), and assume `AbelianSchemePropertyBundle`: $f$ is smooth and proper with connected fibres and admits a relative group law; assume moreover each fibre $f^{-1}(s)$ has topological Krull dimension $2$. Let $i$ be a `LatticeAction` of $\Lambda$ on $(f,L)$: endomorphisms $\mathrm{act}(x)$ of $A$ over $\operatorname{Spec} S$, additive in $x$ on points, with $\mathrm{act}(xy) = \mathrm{act}(x) \circ \mathrm{act}(y)$, $\mathrm{act}(1) = \mathrm{id}$, each compatible with $L$. Assume the trace condition `htr`: for every algebraically closed field $k$, ring map $sk : S \to k$, finite-dimensional $k$-space $V$ and injective $\tau : V \to$ points of $f$ over the dual-number base $\mathrm{tangentBase}\,k\,sk$ whose image is exactly the tangent vectors at the unit, which is additive for $L$ and $k$-homogeneous via $\mathrm{tangentScale}$, and for every $x \in \Lambda$ and $k$-linear $\Phi$ on $V$ induced by $\mathrm{act}(x)$ under $\tau$, if $x + \bar{x} = n$ with $n \in \mathbb{Z}$ then $\operatorname{tr}_k \Phi = n$ in $k$. The conclusion is twofold: there exists a module $\mathcal{L}$ on $A$ with `IsCanonicalPolData f L i.act i.act_over star`, that is, $\mathcal{L}$ is invertible, is symmetric in the sense that its pullback along the inversion morphism of $L$ is isomorphic to $\mathcal{L}$ locally over the base, its kernel is two-torsion, there is a faithfully flat $S$-algebra $S'$ over which $\mathcal{L}$ becomes (locally over the base) $\mathcal{L}_0 \otimes (-1)^*\mathcal{L}_0$ for some invertible $\mathcal{L}_0$ with trivial kernel, for every algebraically closed field $k$ and $sk : S \to k$ the geometric fibre $H^0$ has positive finrank, and $\mathcal{L}$ is Rosati-compatible with the action and $\mathrm{star}$; and any two such $\mathcal{L}, \mathcal{L}'$ are `LocIsoOnBase`, i.e. every point of $\operatorname{Spec} S$ has an open neighbourhood $U$ over which the restrictions of $\mathcal{L}$ and $\mathcal{L}'$ to $f^{-1}(U)$ become isomorphic.
--
--   This is the existence and local-on-the-base uniqueness of the canonical polarisation attached to an action of a maximal order in an indefinite quaternion algebra on an abelian surface, stated for a bare action datum rather than for a fake elliptic curve with level structure. It is used in the construction of the polarised abelian scheme attached to the Čerednik–Drinfeld uniformisation, feeding the closed-immersion/trace criterion for polarised abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_LatticeAction_exists_isCanonicalPolData_and_forall_locIsoOnBase_of_isUnit_two.lean

import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_CerednikDrinfeld_QMLatticeAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.LatticeAction.exists_isCanonicalPolData_and_forall_locIsoOnBase_of_isUnit_two
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (S : Type) [CommRing S] (h2 : IsUnit (2 : S))
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f) (hL : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle S f)
    (hdim : ∀ s : ↥(Spec (CommRingCat.of S)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = 2)
    (i : LatticeAction Λ f L)
    (htr : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k)
      (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) f),
      Function.Injective τ →
      (∀ P : SchemeHomOver (tangentBase k sk) f, P ∈ Set.range τ ↔ IsTangentVector L k sk P) →
      (∀ v w : V, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w)) →
      (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
      ∀ (x : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (i.act x) (i.act_over x) (τ v)) →
      ∀ n : ℤ, (x : ℍ[ℚ, a, b]) + Star.star (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
        LinearMap.trace k V Φ = (n : k)) :
    (∃ 𝓛 : A.Modules, CerednikDrinfeld.QM.IsCanonicalPolData f L i.act i.act_over star 𝓛) ∧
    (∀ 𝓛 𝓛' : A.Modules, CerednikDrinfeld.QM.IsCanonicalPolData f L i.act i.act_over star 𝓛 →
      CerednikDrinfeld.QM.IsCanonicalPolData f L i.act i.act_over star 𝓛' → LocIsoOnBase f 𝓛 𝓛') := by sorry
