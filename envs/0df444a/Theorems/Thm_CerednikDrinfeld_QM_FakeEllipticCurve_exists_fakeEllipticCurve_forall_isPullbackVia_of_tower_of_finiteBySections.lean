-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fakeEllipticCurve_forall_isPullbackVia_of_tower_of_finiteBySections
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_fakeEllipticCurve_forall_isPullbackVia_of_tower_of_finiteBySections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/f2c952bf-bc77-5cff-8de9-9b5f57ba5dbb
-- title:
--   Algebraisation of an adic tower of fake elliptic curves
-- statement:
--   Fix distinct primes $q,q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0<a$ or $0<b$) and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, its completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ which is an order maximal among orders containing it, let $\mu\in\Lambda$ satisfy $\mu^2=-(qq')\cdot 1$, and let $\mathrm{star}:\Lambda\to\Lambda$ satisfy $\mu\,\mathrm{star}(x)=\bar x\,\mu$. Let $R$ be a noetherian local ring, complete for the adic topology of its maximal ideal $\mathfrak m$, equipped with ring maps $\pi_n:R/\mathfrak m^{n+2}\to R/\mathfrak m^{n+1}$ compatible with the quotient maps from $R$. Given level-$1$ fake elliptic curves $E_n$ for $\Lambda$ over $R/\mathfrak m^{n+1}$ and morphisms $t_n:(E_n).A\to(E_{n+1}).A$ which exhibit $E_n$ as the base change of $E_{n+1}$ along $\mathrm{Spec}(\pi_n)$ (a pullback square, compatibility with the relative group laws on $T$-points, with the $\Lambda$-actions, and lifting of points factoring through the level datum), together with modules $\mathcal L_n$ on $(E_n).A$ that are invertible (locally isomorphic to the unit sheaf) with $t_n^{*}\mathcal L_{n+1}\cong\mathcal L_n$, and such that $\mathcal L_0\otimes\mathcal L_0\otimes\mathcal L_0$ is finite by sections over $(E_0).f$ (it admits a presentation by $N+1$ global sections whose associated morphism to projective space over $R/\mathfrak m$ is finite), the conclusion asserts the existence of a level-$1$ fake elliptic curve $E_R$ for $\Lambda$ over $R$ and morphisms $j_n:(E_n).A\to E_R.A$ exhibiting each $E_n$ as the base change of $E_R$ along $R\to R/\mathfrak m^{n+1}$ in the same sense, with $t_n$ followed by $j_{n+1}$ equal to $j_n$, and of an invertible module $\mathcal M$ on $E_R.A$ with $j_n^{*}\mathcal M\cong\mathcal L_n$ for all $n$.
--
--   This is the algebraisation (formal GAGA) step for fake elliptic curves: a compatible tower of level-$1$ fake elliptic curves over the quotients $R/\mathfrak m^{n+1}$, carrying a compatible system of invertible modules whose cube is finite by sections on the bottom layer, comes from a single fake elliptic curve over $R$ together with an invertible module. It is used in the construction of fake elliptic curves over complete discrete valuation rings from data over the residue field, in both the residue characteristic cases treated separately.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fakeEllipticCurve_forall_isPullbackVia_of_tower_of_finiteBySections.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_fakeEllipticCurve_forall_isPullbackVia_of_tower_of_finiteBySections
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

    (π : ∀ n : ℕ, (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1)) →+* (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))
    (hπ : ∀ n, (π n).comp (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1 + 1))) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))

    (E : ∀ n : ℕ, FakeEllipticCurve Λ 1 (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))
    (t : ∀ n : ℕ, (E n).A ⟶ (E (n + 1)).A)
    (ht : ∀ n, FakeEllipticCurve.IsPullbackVia (π n) (E (n + 1)) (E n) (t n))

    (𝓛 : ∀ n : ℕ, (E n).A.Modules)
    (hinv : ∀ n, Scheme.Modules.IsInvertible (𝓛 n))
    (hcompat : ∀ n, Nonempty ((Scheme.Modules.pullback (t n)).obj (𝓛 (n + 1)) ≅ 𝓛 n))
    (hample : Scheme.Modules.FiniteBySections ((𝓛 0) ⊗ (𝓛 0) ⊗ (𝓛 0)) (E 0).f) :
    ∃ (ER : FakeEllipticCurve Λ 1 R) (j : ∀ n : ℕ, (E n).A ⟶ ER.A),
      (∀ n, FakeEllipticCurve.IsPullbackVia (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))) ER (E n) (j n)) ∧
      (∀ n, t n ≫ j (n + 1) = j n) ∧
      ∃ 𝓜 : ER.A.Modules, Scheme.Modules.IsInvertible 𝓜 ∧
        ∀ n, Nonempty ((Scheme.Modules.pullback (j n)).obj 𝓜 ≅ 𝓛 n) := by sorry
