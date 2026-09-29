-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isInvertible_compatible_finiteBySections_of_tower_versal_of_ne_of_isUnit_two
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isInvertible_compatible_finiteBySections_of_tower_versal_of_ne_of_isUnit_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/d6768898-8ec8-5381-b6d1-664948ded69b
-- title:
--   Compatible invertible sheaves along a versal tower of fake elliptic curves
-- statement:
--   Fix distinct primes $q\neq q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0<a$ or $0<b$) and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is an order, maximal among orders for inclusion, let $\mu\in\Lambda$ satisfy $\mu^2=-(qq')\cdot 1$, and let $\mathrm{star}:\Lambda\to\Lambda$ satisfy $\mu\,\mathrm{star}(x)=\bar x\,\mu$ for all $x\in\Lambda$. Fix a level $N$ and a prime $p$ with $p\neq q$, $p\neq q'$, $p\nmid N$. Let $R$ be a Noetherian local ring, adically complete for its maximal ideal $\mathfrak{m}$, with algebraically closed residue field of characteristic $p$, in which $2$ is a unit, and let $\pi_n:R/\mathfrak{m}^{n+2}\to R/\mathfrak{m}^{n+1}$ be ring maps commuting with the quotient maps. Given fake elliptic curves $E_n$ of level $N$ with $\Lambda$-action over $R/\mathfrak{m}^{n+1}$ and morphisms $t_n:(E_n).A\to(E_{n+1}).A$ exhibiting $E_n$ as the base change of $E_{n+1}$ along $\pi_n$ (a pullback square compatible with the relative group laws, the $\Lambda$-actions and the level structures), and assuming the tower is versal at the bottom in the sense that for every Artinian local $B$, every surjection $\rho:B\to R/\mathfrak{m}$ with kernel the maximal ideal of $B$, and every fake elliptic curve $E'$ over $B$ together with $g':(E_0).A\to E'.A$ making $E_0$ the base change of $E'$ along $\rho$, there are $n$, a ring map $\varphi:R/\mathfrak{m}^{n+1}\to B$ and $h:E'.A\to(E_n).A$ making $E'$ the base change of $E_n$ along $\varphi$: then there exist modules $\mathcal{L}_n$ on $(E_n).A$ which are invertible (each point has an open neighbourhood on which the restriction is isomorphic to the unit module), with $t_n^{*}\mathcal{L}_{n+1}\cong\mathcal{L}_n$ for all $n$, and such that $\mathcal{L}_0\otimes\mathcal{L}_0\otimes\mathcal{L}_0$ is finite by sections over $(E_0).f$, that is, admits a Proj presentation by $N'+1$ sections whose associated morphism to projective space over the base is finite. The conclusion records no compatibility of the $\mathcal{L}_n$ with the involution $\mathrm{star}$.
--
--   This is the step asserting that a polarisation rides along a versal deformation tower: over a complete Noetherian local base with algebraically closed residue field of residue characteristic prime to the discriminant $qq'$ and to the level, a compatible system of invertible sheaves with finiteness of the triple tensor power at the bottom level exists on a versal tower of fake elliptic curves. It feeds the construction of pullback data over discrete valuation rings of characteristic zero used in the Čerednik–Drinfeld analysis of Shimura curves attached to the indefinite quaternion algebra ramified exactly at $q$ and $q'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isInvertible_compatible_finiteBySections_of_tower_versal_of_ne_of_isUnit_two.lean

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
open IsLocalRing
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isInvertible_compatible_finiteBySections_of_tower_versal_of_ne_of_isUnit_two
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (p : ℕ) [Fact p.Prime] (hpq : p ≠ q) (hpq' : p ≠ q') (hpN : ¬ p ∣ N)
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    [IsAlgClosed (ResidueField R)] [CharP (ResidueField R) p] (h2 : IsUnit (2 : R))
    (π : ∀ n : ℕ, (R ⧸ maximalIdeal R ^ (n + 1 + 1)) →+* (R ⧸ maximalIdeal R ^ (n + 1)))
    (hπ : ∀ n, (π n).comp (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1 + 1))) = Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)))
    (E : ∀ n : ℕ, FakeEllipticCurve Λ N (R ⧸ maximalIdeal R ^ (n + 1)))
    (t : ∀ n : ℕ, (E n).A ⟶ (E (n + 1)).A)
    (ht : ∀ n, FakeEllipticCurve.IsPullbackVia (π n) (E (n + 1)) (E n) (t n))

    (hversal : ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B]
      (ρ : B →+* (R ⧸ maximalIdeal R ^ (0 + 1))) (hρ : Function.Surjective ρ) (hρker : RingHom.ker ρ = maximalIdeal B)
      (E' : FakeEllipticCurve Λ N B) (g' : (E 0).A ⟶ E'.A) (hg' : FakeEllipticCurve.IsPullbackVia ρ E' (E 0) g'),
      ∃ (n : ℕ) (φ : (R ⧸ maximalIdeal R ^ (n + 1)) →+* B) (h : E'.A ⟶ (E n).A),
        FakeEllipticCurve.IsPullbackVia φ (E n) E' h) :
    ∃ (𝓛 : ∀ n : ℕ, (E n).A.Modules),
      (∀ n, Scheme.Modules.IsInvertible (𝓛 n)) ∧
      (∀ n, Nonempty ((Scheme.Modules.pullback (t n)).obj (𝓛 (n + 1)) ≅ 𝓛 n)) ∧
      Scheme.Modules.FiniteBySections ((𝓛 0) ⊗ (𝓛 0) ⊗ (𝓛 0)) (E 0).f := by sorry
