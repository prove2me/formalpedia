-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_tower_isPullbackVia_isInvertible_rosatiCompatible_of_isFormalModuleVia_of_forall_map_eq
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_tower_isPullbackVia_isInvertible_rosatiCompatible_of_isFormalModuleVia_of_forall_map_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/f4408cd2-c994-577d-b7e0-153b88d57e88
-- title:
--   Compatible tower of Rosati-polarised fake elliptic curves over O'/𝔪ⁿ⁺¹
-- statement:
--   Fix distinct primes $q,q'$ and rationals $a,b$ such that $\mathbb H[\mathbb Q,a,b]$ is indefinite ($0<a$ or $0<b$) and, for each height-one prime $v$ of $\mathcal O_{\mathbb Q}$, every nonzero element of $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ be a $\mathbb Z$-submodule which is an order (containing $1$, closed under multiplication, $\mathbb Q$-spanning, finitely generated) and maximal among orders, let $\mu\in\Lambda$ satisfy $\mu^2=-(qq')\cdot 1$, and let $\mathrm{star}:\Lambda\to\Lambda$ satisfy $\mu\,\mathrm{star}(x)=\bar x\,\mu$ for all $x\in\Lambda$; assume $1\in\Lambda$. Let $p$ be a prime with $p=q$ or $p=q'$ and let $\mathrm{coord}:\Lambda\to W(\mathbb F_{p^2})^2$ satisfy `IsOrderCoord`: it is additive and injective, sends $1$ to $(1,0)$, is multiplicative in the Frobenius-twisted sense $(\alpha_1\beta_1+p\,\alpha_2\varphi(\beta_2),\ \alpha_1\beta_2+\alpha_2\varphi(\beta_1))$, has dense image modulo every power of $p$, and matches reduced traces. Let $O'$ be a noetherian local ring with algebraically closed residue field and $p\in\mathfrak m_{O'}$, and let $\pi_n:O'/\mathfrak m^{n+2}\to O'/\mathfrak m^{n+1}$ be ring homomorphisms compatible with the quotient maps. Let $X_n$ be formal $\mathcal O_D$-modules over $O'/\mathfrak m^{n+1}$ (two-dimensional commutative formal group laws with a $W(\mathbb F_{p^2})$-action and a series $\varpi$ with $\varpi\circ\varpi=[p]$ and $\varpi\circ[a]=[\varphi(a)]\circ\varpi$) with $X_{n+1}$ base-changed along $\pi_n$ equal to $X_n$. Finally let $E_0$ be a fake elliptic curve for $\Lambda$ of level $1$ over $O'/\mathfrak m$ together with formal coordinates $\theta_0$ of dimension $2$ on $E_0.f$ such that `IsFormalModuleVia` holds: $\theta_0$ is a system of formal coordinates for the relative group law $E_0.L$ with formal group $X_0.F$, and the action of each $m\in\Lambda$ on nilpotent points corresponds to the series $[\,\mathrm{coord}(m)_1\,]+_{X_0.F}[\,\mathrm{coord}(m)_2\,]\circ\varpi$; and let $\mathcal L_0$ be an invertible module on $E_0.A$ that is Rosati-compatible for $\mathrm{star}$, i.e. for every $b\in\Lambda$ the pullbacks of the Mumford bundle of $\mathcal L_0$ along $(\mathrm{pr}_1,\mathrm{act}(b)\circ\mathrm{pr}_2)$ and along $(\mathrm{act}(\mathrm{star}\,b)\circ\mathrm{pr}_1,\mathrm{pr}_2)$ are isomorphic locally over the base. Then there exist fake elliptic curves $E_n$ for $\Lambda$ of level $1$ over $O'/\mathfrak m^{n+1}$, morphisms $t_n:(E_n).A\to(E_{n+1}).A$ and modules $\mathcal L_n$ on $(E_n).A$ such that $E_0$ is the given curve, each $t_n$ exhibits $E_n$ as the base change of $E_{n+1}$ along $\pi_n$ in the sense of `IsPullbackVia` (the square of $t_n$, $(E_n).f$, $(E_{n+1}).f$ and $\mathrm{Spec}(\pi_n)$ is a pullback, $t_n$ is compatible with the group laws and with the $\Lambda$-actions, and points of $E_n$ factoring through its level scheme map into that of $E_{n+1}$), each $\mathcal L_n$ is invertible and Rosati-compatible for $\mathrm{star}$, the pullback of $\mathcal L_{n+1}$ along $t_n$ is isomorphic to $\mathcal L_n$, and $\mathcal L_0$ agrees with the given bundle (as a heterogeneous equality, the two living over the identified schemes).
--
--   This is the Serre–Tate style deformation tower for fake elliptic curves with quaternionic multiplication: a one-step lifting result across the square-zero extension $O'/\mathfrak m^{n+2}\to O'/\mathfrak m^{n+1}$, together with the rigidity supplied by the formal $\mathcal O_D$-module structure, is iterated to produce a full compatible system over the artinian quotients of $O'$, carrying the invertible Rosati-compatible bundles along. It feeds the construction of a fake elliptic curve over a discrete valuation ring of characteristic zero reducing to a given one in characteristic $p$, a step in the Čerednik–Drinfeld description of Shimura curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_tower_isPullbackVia_isInvertible_rosatiCompatible_of_isFormalModuleVia_of_forall_map_eq.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Polarisation
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_tower_isPullbackVia_isInvertible_rosatiCompatible_of_isFormalModuleVia_of_forall_map_eq
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    {p : ℕ} [Fact p.Prime] (hp : p = q ∨ p = q')
    (coord : ↥Λ → Zp2 p × Zp2 p) (hcoord : IsOrderCoord Λ p coord)
    (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ)

    (O' : Type) [CommRing O'] [IsLocalRing O'] [IsNoetherianRing O'] [IsAlgClosed (ResidueField O')]
    (hpO : ((p : ℕ) : O') ∈ maximalIdeal O')

    (π : ∀ n : ℕ, (O' ⧸ maximalIdeal O' ^ (n + 1 + 1)) →+* (O' ⧸ maximalIdeal O' ^ (n + 1)))
    (hπ : ∀ n, (π n).comp (Ideal.Quotient.mk (maximalIdeal O' ^ (n + 1 + 1))) = Ideal.Quotient.mk (maximalIdeal O' ^ (n + 1)))

    (X : ∀ n : ℕ, FormalODModule p (O' ⧸ maximalIdeal O' ^ (n + 1)))
    (hX : ∀ n, (X (n + 1)).map (π n) = X n)

    (E₀ : FakeEllipticCurve Λ 1 (O' ⧸ maximalIdeal O' ^ (0 + 1))) (θ₀ : RelativeGroupLaw.FormalCoordinates E₀.f 2)
    (h₀ : E₀.IsFormalModuleVia coord (X 0) θ₀)
    (𝓛₀ : E₀.A.Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀)
    (hR₀ : RosatiCompatible E₀.f E₀.L 𝓛₀ E₀.act E₀.act_over star) :
    ∃ (E : ∀ n : ℕ, FakeEllipticCurve Λ 1 (O' ⧸ maximalIdeal O' ^ (n + 1)))
      (t : ∀ n : ℕ, (E n).A ⟶ (E (n + 1)).A)
      (𝓛 : ∀ n : ℕ, (E n).A.Modules),
      E 0 = E₀ ∧
      (∀ n, FakeEllipticCurve.IsPullbackVia (π n) (E (n + 1)) (E n) (t n)) ∧
      (∀ n, Scheme.Modules.IsInvertible (𝓛 n)) ∧
      (∀ n, RosatiCompatible (E n).f (E n).L (𝓛 n) (E n).act (E n).act_over star) ∧
      (∀ n, Nonempty ((Scheme.Modules.pullback (t n)).obj (𝓛 (n + 1)) ≅ 𝓛 n)) ∧
      HEq (𝓛 0) 𝓛₀ := by sorry
