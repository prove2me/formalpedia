-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_inv_act_forall_comp_eq_of_tower_of_forall_isPullback
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_inv_act_forall_comp_eq_of_tower_of_forall_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/c9961b97-77ab-589c-941f-c57d57277f70
-- title:
--   Algebraising inversion and Λ-action along a fake elliptic tower
-- statement:
--   Fix distinct primes $q,q'$ and rationals $a,b$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`: $0<a$ or $0<b$, and for every height-one prime $v$ of the integers of $\mathbb{Q}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit exactly when $v$ divides $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is a maximal order (an order: containing $1$, multiplicatively closed, $\mathbb{Q}$-spanning and finitely generated, and maximal among such), let $\mu\in\Lambda$ satisfy $\mu^2=-(qq')\cdot 1$, and let $\mathrm{star}:\Lambda\to\Lambda$ satisfy $\mu\cdot\mathrm{star}(x)=\bar{x}\mu$ for all $x\in\Lambda$. Let $R$ be a noetherian local ring, complete for the $\mathfrak{m}$-adic topology, write $R_n=R/\mathfrak{m}^{n+1}$, and let $\pi_n:R_{n+1}\to R_n$ be ring maps compatible with the quotient maps from $R$. Let $E_n$ be a fake elliptic curve of level $1$ for $\Lambda$ over $R_n$ (a smooth proper scheme $A_n\to\operatorname{Spec}R_n$ with connected fibres of dimension $2$, a commutative relative group law $L_n$, an action of $\Lambda$ by base-preserving endomorphisms, and the remaining level data), and let $t_n:A_n\to A_{n+1}$ satisfy `IsPullbackVia` $(\pi_n)$: $t_n$ makes $A_n$ the fibre product of $A_{n+1}$ with $\operatorname{Spec}R_n$ over $\operatorname{Spec}R_{n+1}$, is compatible with the group laws and the $\Lambda$-actions, and carries points factoring through the level structure of $E_n$ to points factoring through that of $E_{n+1}$. Let $Z$ be a scheme with a finite morphism $G$ to $\mathbb{P}^r_R=\operatorname{Proj}$ of the homogeneous polynomials in $r+1$ variables over $R$, and let $j_n:A_n\to Z$ satisfy $t_n$ followed by $j_{n+1}$ equals $j_n$ and make each square formed by $j_n$, $A_n\to\operatorname{Spec}R_n$, the structure map $G$ followed by $\mathbb{P}^r_R\to\operatorname{Spec}R$, and $\operatorname{Spec}R_n\to\operatorname{Spec}R$ a pullback. Then there are a morphism $\iota:Z\to Z$ and a family $\mathrm{act}:\Lambda\to(Z\to Z)$, all over $\operatorname{Spec}R$, such that for every $n$, every scheme $T$ with a map $t'$ to $\operatorname{Spec}R_n$ and every $T$-point $P$ of $A_n$ over $t'$, the $L_n$-inverse of $P$ composed with $j_n$ equals $P$ followed by $j_n$ and then $\iota$, and such that for every $n$ and $x\in\Lambda$ the action of $x$ on $A_n$ followed by $j_n$ equals $j_n$ followed by $\mathrm{act}(x)$.
--
--   This is the algebraisation step transferring the inversion and the quaternionic action of a tower of fake elliptic curves over the truncations $R/\mathfrak{m}^{n+1}$ to endomorphisms of the total space $Z$, which is finite over $\mathbb{P}^r_R$; it rests on the formal existence theorem for morphisms of schemes finite over projective space over a complete local noetherian ring. It is used in assembling the full group and $\Lambda$-module structure on $Z$ in the Čerednik–Drinfeld uniformisation of quaternionic Shimura curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_inv_act_forall_comp_eq_of_tower_of_forall_isPullback.lean

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
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open AlgebraicGeometry

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_inv_act_forall_comp_eq_of_tower_of_forall_isPullback
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
    ∃ (ι : Z ⟶ Z) (hι : ι ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r)) (act : ↥Λ → (Z ⟶ Z)) (act_over : ∀ x : ↥Λ, act x ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r)),
      (∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P : SchemeHomOver t' (E n).f),
        ((E n).L.inv t' P).1 ≫ jz n = (P.1 ≫ jz n) ≫ ι) ∧
      (∀ (n : ℕ) (x : ↥Λ), (E n).act x ≫ jz n = jz n ≫ act x) := by sorry
