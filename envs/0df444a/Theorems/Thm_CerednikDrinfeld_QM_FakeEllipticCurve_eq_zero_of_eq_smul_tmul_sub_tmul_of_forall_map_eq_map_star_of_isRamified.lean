-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_eq_zero_of_eq_smul_tmul_sub_tmul_of_forall_map_eq_map_star_of_isRamified
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.eq_zero_of_eq_smul_tmul_sub_tmul_of_forall_map_eq_map_star_of_isRamified
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/f555c653-4ac5-592e-b151-4fb1729e523e
-- title:
--   Vanishing of ⋆-balanced alternating tensors at a ramified prime
-- statement:
--   Fix primes $q\neq q'$ and rationals $a,b$ such that $\mathbb H[\mathbb Q,a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`: $a>0$ or $b>0$, and for each height-one prime $v$ of $\mathcal O_{\mathbb Q}$ every nonzero element of $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ is a unit exactly when $q\in v$ or $q'\in v$. Let $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ be a $\mathbb Z$-submodule that is an order maximal among orders containing it, $\mu\in\Lambda$ with $\mu^2=-(qq')\cdot 1$, and $\star\colon\Lambda\to\Lambda$ any map with $\mu\,x^\star=\bar x\,\mu$. Let $N\in\mathbb N$, let $p$ be a prime with $p=q$ or $p=q'$, let $k$ be an algebraically closed field of characteristic $p$, let $E$ be a fake elliptic curve of level $N$ over $k$ with $\Lambda$-action `E.act`, and let $\mathcal K$ be a finite ordered affine cover of `E.A`. Let $H$ be a $k$-vector space, $A_1\subseteq H$ a subspace, and $\mathrm{cls}$ a $k$-linear map from the kernel of the degree-one Čech differential of the structure presheaf `OModulePresheaf.unit E.f` on $\mathcal K$ to $H$, with image $A_1$ and with kernel precisely the degree-one Čech coboundaries. Let $\Phi\colon\Lambda\to\operatorname{End}_k(H)$ preserve $A_1$ and be, on $A_1$, additive, unital and anti-multiplicative ($\Phi(xy)h=\Phi(y)(\Phi(x)h)$), and be geometrically pinned: for all $x\in\Lambda$, every ordered affine cover $\mathcal W$ of `E.A`, all index maps $\lambda,\lambda'$ refining $\mathcal W$ into $\mathcal K$ along `E.act x` and along the identity respectively, and all cocycles $z,z'$, if the difference of the `unitPullback` of $z$ along `E.act x` and of $z'$ along the identity is a coboundary on $\mathcal W$, then $\Phi(x)(\mathrm{cls}\,z)=\mathrm{cls}\,z'$. Then for $a_1,a_2\in A_1$, $c\in k$ and $t=c\,(a_1\otimes a_2-a_2\otimes a_1)\in H\otimes_k H$ satisfying $(\mathrm{id}\otimes\Phi(x))t=(\Phi(x^\star)\otimes\mathrm{id})t$ for all $x\in\Lambda$, one has $t=0$.
--
--   This is the vanishing step for alternating, $\star$-balanced tensors in $\check H^1(\mathcal O_E)\otimes\check H^1(\mathcal O_E)$ when the residue characteristic divides the discriminant of the quaternion algebra, the quaternionic analogue of the Rosati-involution rigidity used for fake elliptic curves; its content is that the quaternionic action on the two-dimensional space $A_1$ admits no such invariant alternating tensor. It is cited in the construction of an invertible pullback isomorphism for Rosati-compatible data over Artinian bases with algebraically closed residue field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_eq_zero_of_eq_smul_tmul_sub_tmul_of_forall_map_eq_map_star_of_isRamified.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.eq_zero_of_eq_smul_tmul_sub_tmul_of_forall_map_eq_map_star_of_isRamified
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    {N : ℕ} {p : ℕ} [Fact p.Prime] (hp : p = q ∨ p = q')
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
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

    (t : H ⊗[k] H) (a₁ a₂ : H) (ha₁ : a₁ ∈ A₁) (ha₂ : a₂ ∈ A₁) (c : k)
    (ht : t = c • (a₁ ⊗ₜ[k] a₂ - a₂ ⊗ₜ[k] a₁))
    (hbal : ∀ x : ↥Λ,
      TensorProduct.map LinearMap.id (Φ x) t = TensorProduct.map (Φ (star x)) LinearMap.id t) :
    t = 0 := by sorry
