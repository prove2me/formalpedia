-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fakeEllipticCurve_forall_isPullbackVia_of_tower_of_forall_isPullback
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_fakeEllipticCurve_forall_isPullbackVia_of_tower_of_forall_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/960af84b-5129-59c7-960a-2fb5780e3911
-- title:
--   Algebraisation of a tower of fake elliptic curves
-- statement:
--   Fix distinct primes $q\neq q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$, and for every finite place $v$ of $\mathbb{Q}$ the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ lies over $q$ or over $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ that is a maximal order (containing $1$, closed under multiplication, $\mathbb{Q}$-spanning, finitely generated, and maximal among such), let $\mu\in\Lambda$ satisfy $\mu^2=-(qq')\cdot 1$, and let $\mathrm{star}:\Lambda\to\Lambda$ satisfy $\mu\,\mathrm{star}(x)=\bar{x}\mu$ for all $x\in\Lambda$. Let $R$ be a noetherian local ring, complete for the $\mathfrak{m}$-adic topology, $\mathfrak m$ its maximal ideal, with ring maps $\pi_n:R/\mathfrak m^{n+2}\to R/\mathfrak m^{n+1}$ compatible with the quotient maps. Let $E_n$ be fake elliptic curves for $\Lambda$ with level parameter $1$ over $R/\mathfrak m^{n+1}$ and $t_n:(E_n).A\to(E_{n+1}).A$ morphisms exhibiting each $E_n$ as the base change of $E_{n+1}$ along $\pi_n$ in the sense of `FakeEllipticCurve.IsPullbackVia`: the square of $t_n$ over $\mathrm{Spec}$ of $\pi_n$ is a pullback, $t_n$ is a homomorphism for the relative group laws and commutes with the $\Lambda$-actions, and points of $(E_{n+1})$ factoring through its level section are carried to points factoring through that of $E_n$. Let $r\in\mathbb{N}$, let $Z$ be a scheme and $G:Z\to\mathbb{P}^r_R$ a finite morphism, and let $jz_n:(E_n).A\to Z$ satisfy $jz_{n+1}\circ t_n=jz_n$ and make each square formed by $jz_n$, $(E_n).f$, the composite of $G$ with the structure morphism $\mathbb{P}^r_R\to\mathrm{Spec}\,R$, and $\mathrm{Spec}$ of $R\to R/\mathfrak m^{n+1}$ a pullback. Then there exist a fake elliptic curve $E_R$ for $\Lambda$ with level parameter $1$ over $R$ and morphisms $j_n:(E_n).A\to (E_R).A$ such that each $j_n$ exhibits $E_n$ as the base change of $E_R$ along $R\to R/\mathfrak m^{n+1}$ in the above sense, and $j_{n+1}\circ t_n=j_n$.
--
--   This is the algebraisation step in the Čerednik–Drinfeld part of the development: a formal tower of fake elliptic curves over the truncations $R/\mathfrak m^{n+1}$, realised inside a scheme finite over projective space, comes from a single fake elliptic curve over the complete local base. It is used by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_fakeEllipticCurve_forall_isPullbackVia_of_tower_of_isFinite_proj`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_fakeEllipticCurve_forall_isPullbackVia_of_tower_of_isFinite_proj).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fakeEllipticCurve_forall_isPullbackVia_of_tower_of_forall_isPullback.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_fakeEllipticCurve_forall_isPullbackVia_of_tower_of_forall_isPullback
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
    {r : ℕ}
    (Z : Scheme.{0}) (G : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R)) [IsFinite G] (jz : ∀ n : ℕ, (E n).A ⟶ Z)
    (hZ :
      (∀ n, t n ≫ jz (n + 1) = jz n) ∧
      (∀ n, CategoryTheory.IsPullback (jz n) (E n).f (G ≫ ProjSpace.π R r) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))))))) :
    ∃ (ER : FakeEllipticCurve Λ 1 R) (j : ∀ n : ℕ, (E n).A ⟶ ER.A),
      (∀ n, FakeEllipticCurve.IsPullbackVia (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))) ER (E n) (j n)) ∧
      (∀ n, t n ≫ j (n + 1) = j n) := by sorry
