-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_eq_zero_of_eq_smul_tmul_sub_tmul_of_forall_map_eq_map_star_of_isSplit_of_charP
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.eq_zero_of_eq_smul_tmul_sub_tmul_of_forall_map_eq_map_star_of_isSplit_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/222c7511-b123-5e5a-a1c6-87c7d206d28a
-- title:
--   Vanishing of star-balanced alternating tensors for non-scalar Φ(μ)
-- statement:
--   Let $q\neq q'$ be primes and $a,b\in\mathbb{Q}$ be such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`: $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is an order maximal among the orders containing it, let $\mu\in\Lambda$ satisfy $\mu^2=-(qq')\cdot 1$, and let $\mathrm{star}\colon\Lambda\to\Lambda$ be a map with $\mu\cdot\mathrm{star}(x)=\bar{x}\mu$ for all $x\in\Lambda$. Let $k$ be an algebraically closed field of characteristic $p$ in which $qq'$ is invertible, let $E$ be a fake elliptic curve over $k$ of level $N$ with $\Lambda$-action (an abelian scheme $E.A\to\operatorname{Spec}k$ with commutative relative group law, two-dimensional fibres and an action $x\mapsto E.\mathrm{act}\,x$ of $\Lambda$), and let $\mathcal{K}$ be a finite linearly ordered affine open cover of $E.A$. Let $H$ be a $k$-vector space and $A_1\subseteq H$ a subspace, realised as first Čech cohomology of the structure sheaf: a $k$-linear $\mathrm{cls}$ from the kernel of the first differential $d^1$ of the Čech complex of `OModulePresheaf.unit E.f` on $\mathcal{K}$ to $H$, with image $A_1$, whose kernel consists exactly of the cocycles in the image of $d^0$. Let $\Phi\colon\Lambda\to\operatorname{End}_k(H)$ preserve $A_1$ and satisfy, on elements of $A_1$, additivity in $x$, $\Phi(1)=\mathrm{id}$ and $\Phi(xy)h=\Phi(y)(\Phi(x)h)$, and be induced by pullback of cocycles: for every $x\in\Lambda$, every ordered affine cover $\mathcal{W}$ of $E.A$, index maps $\lambda,\lambda'\colon\mathcal{W}.\iota\to\mathcal{K}.\iota$ with $\mathcal{W}.U\,w$ contained in $(E.\mathrm{act}\,x)^{-1}\mathcal{K}.U(\lambda w)$, resp. in $\mathcal{K}.U(\lambda' w)$, and cocycles $z,z'$, if the difference of the degree-one `unitPullback` of $z$ along $E.\mathrm{act}\,x$ and of $z'$ along the identity lies in the image of $d^0$ on $\mathcal{W}$, then $\Phi(x)(\mathrm{cls}\,z)=\mathrm{cls}\,z'$. Assume there is no $c_0\in k$ with $\Phi(\mu)h=c_0 h$ for all $h\in A_1$. Then any $t\in H\otimes_k H$ of the form $t=c\,(a_1\otimes a_2-a_2\otimes a_1)$ with $a_1,a_2\in A_1$, $c\in k$, satisfying $(\mathrm{id}\otimes\Phi(x))t=(\Phi(\mathrm{star}\,x)\otimes\mathrm{id})t$ for all $x\in\Lambda$, is zero.
--
--   This is the vanishing step for alternating $\star$-balanced tensors on the first Čech cohomology of the structure sheaf of a fake elliptic curve in residue characteristic $p$ coprime to the discriminant $qq'$: the quaternionic action forces any such tensor to vanish unless $\mu$ acts as a scalar. It is used in the construction of a Rosati-compatible invertible pullback isomorphism for fake elliptic curves, via the two-dimensionality of the cohomology and the classification of the induced two-dimensional representations of $\Lambda$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_eq_zero_of_eq_smul_tmul_sub_tmul_of_forall_map_eq_map_star_of_isSplit_of_charP.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra
  CerednikDrinfeld CerednikDrinfeld.QM IsLocalRing AlgebraicGeometry.Polarisation AlgebraicGeometry.SmallExtension
open scoped Quaternion TensorProduct

theorem CerednikDrinfeld.QM.FakeEllipticCurve.eq_zero_of_eq_smul_tmul_sub_tmul_of_forall_map_eq_map_star_of_isSplit_of_charP
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    {N : ℕ} {p : ℕ} [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k p] (hqq : IsUnit ((q * q' : ℕ) : k))
    (E : FakeEllipticCurve Λ N k) (𝒦 : E.A.OrderedAffineCover)

    (H : Type) [AddCommGroup H] [Module k H] (A₁ : Submodule k H)
    (cls : ↥(LinearMap.ker ((OModulePresheaf.unit E.f).d 𝒦 1)) →ₗ[k] H)
    (hrange : LinearMap.range cls = A₁)
    (hker : ∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit E.f).d 𝒦 1)),
      cls z = 0 ↔ (z : (OModulePresheaf.unit E.f).cochain 𝒦 1) ∈ LinearMap.range ((OModulePresheaf.unit E.f).d 𝒦 0))
    (Φ : ↥Λ → (H →ₗ[k] H))
    (hΦA : ∀ (x : ↥Λ), ∀ h ∈ A₁, Φ x h ∈ A₁)
    (hΦ_add : ∀ (x y : ↥Λ), ∀ h ∈ A₁, Φ (x + y) h = Φ x h + Φ y h)
    (hΦ_one : ∀ (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ), ∀ h ∈ A₁, Φ ⟨1, h1⟩ h = h)
    (hΦ_mul : ∀ (x y : ↥Λ) (hxy : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ), ∀ h ∈ A₁,
      Φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hxy⟩ h = Φ y (Φ x h))

    (hΦ : ∀ (x : ↥Λ) (𝒲 : E.A.OrderedAffineCover) (lam lam' : 𝒲.ι → 𝒦.ι)
        (hlam : ∀ w, 𝒲.U w ≤ E.act x ⁻¹ᵁ 𝒦.U (lam w)) (hlam' : ∀ w, 𝒲.U w ≤ (𝟙 E.A) ⁻¹ᵁ 𝒦.U (lam' w))
        (z z' : ↥(LinearMap.ker ((OModulePresheaf.unit E.f).d 𝒦 1))),
        OModulePresheaf.unitPullback (πX := E.f) (E.act x) 𝒲 𝒦 lam hlam 1 z.1 -
            OModulePresheaf.unitPullback (πX := E.f) (𝟙 E.A) 𝒲 𝒦 lam' hlam' 1 z'.1 ∈
          LinearMap.range ((OModulePresheaf.unit E.f).d 𝒲 0) →
        Φ x (cls z) = cls z')

    (hμns : ¬ ∃ c₀ : k, ∀ h ∈ A₁, Φ μ h = c₀ • h)

    (t : H ⊗[k] H) (a₁ a₂ : H) (ha₁ : a₁ ∈ A₁) (ha₂ : a₂ ∈ A₁) (c : k)
    (ht : t = c • (a₁ ⊗ₜ[k] a₂ - a₂ ⊗ₜ[k] a₁))
    (hbal : ∀ x : ↥Λ,
      TensorProduct.map LinearMap.id (Φ x) t = TensorProduct.map (Φ (star x)) LinearMap.id t) :
    t = 0 := by sorry
