-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_finrank_eq_two_and_trace_restrict_eq_of_charP_of_isIndefiniteRamifiedExactlyAt
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.finrank_eq_two_and_trace_restrict_eq_of_charP_of_isIndefiniteRamifiedExactlyAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/4281799b-eea1-5ba5-a6f5-cb73a4692dc3
-- title:
--   Rank two and quaternionic trace on Čech H¹ in characteristic p
-- statement:
--   Let $q\neq q'$ be primes and let $a,b\in\mathbb{Q}$ satisfy `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ divides $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among orders, let $\mu\in\Lambda$ satisfy $\mu^{2}=-(qq')\cdot 1$, and let $\mathrm{star}:\Lambda\to\Lambda$ satisfy $\mu\,\mathrm{star}(x)=\bar{x}\mu$ for all $x\in\Lambda$. Let $N\in\mathbb{N}$, let $p$ be a prime, let $k$ be an algebraically closed field of characteristic $p$, let $E$ be a `FakeEllipticCurve Λ N k` (an abelian scheme $E.f:E.A\to\operatorname{Spec}k$ with commutative relative group law, two-dimensional fibres and a $\Lambda$-action `E.act`), and let $\mathcal{K}$ be a finite ordered affine cover of $E.A$. Let $H$ be a $k$-vector space, $A_1\subseteq H$ a subspace, and $\mathrm{cls}$ a $k$-linear map from the kernel of the first Čech differential of the structure presheaf `OModulePresheaf.unit E.f` on $\mathcal{K}$ to $H$, with image exactly $A_1$ and with $\mathrm{cls}\,z=0$ precisely for $z$ a coboundary; thus $A_1$ realises $H^{1}(\mathcal{K},\mathcal{O})$. Let $\Phi:\Lambda\to\operatorname{End}_k(H)$ preserve $A_1$, be additive on $A_1$, send $1$ to the identity on $A_1$ and satisfy $\Phi(xy)=\Phi(y)\circ\Phi(x)$ on $A_1$, and assume the pinning hypothesis: for every $x\in\Lambda$, every ordered affine cover $\mathcal{W}$ of $E.A$, index maps $\lambda,\lambda'$ refining $\mathcal{W}$ into $\mathcal{K}$ along `E.act x` and along the identity, and cocycles $z,z'$, if the pullback of $z$ along `E.act x` minus the pullback of $z'$ along the identity is a coboundary on $\mathcal{W}$, then $\Phi(x)(\mathrm{cls}\,z)=\mathrm{cls}\,z'$. The conclusion is that $\dim_k A_1=2$ and that for all $m\in\Lambda$ and $n\in\mathbb{Z}$ with $m+\bar m=n$ in $\mathbb{H}[\mathbb{Q},a,b]$, the trace of $\Phi(m)$ restricted to $A_1$ equals the image of $n$ in $k$.
--
--   This is the Eichler–Shimura trace identity for a fake elliptic curve in characteristic $p$: the first cohomology of the structure sheaf is two-dimensional and the induced action of an element $m$ of the maximal order has trace equal to the reduced trace $m+\bar m$, with no restriction on the relation of $p$ to $qq'$. It feeds the rigidity statement [`CerednikDrinfeld.QM.FakeEllipticCurve.eq_zero_of_eq_smul_tmul_sub_tmul_of_forall_map_eq_map_star_of_isRamified`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.eq_zero_of_eq_smul_tmul_sub_tmul_of_forall_map_eq_map_star_of_isRamified) in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_finrank_eq_two_and_trace_restrict_eq_of_charP_of_isIndefiniteRamifiedExactlyAt.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.finrank_eq_two_and_trace_restrict_eq_of_charP_of_isIndefiniteRamifiedExactlyAt
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    {N : ℕ} {p : ℕ} [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
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
        Φ x (cls z) = cls z') :
    Module.finrank k ↥A₁ = 2 ∧
      ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) + Star.star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
        LinearMap.trace k ↥A₁ ((Φ m).restrict (hΦA m)) = (n : k) := by sorry
