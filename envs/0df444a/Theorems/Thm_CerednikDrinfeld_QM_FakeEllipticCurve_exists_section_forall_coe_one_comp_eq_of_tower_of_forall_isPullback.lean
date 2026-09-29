-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_section_forall_coe_one_comp_eq_of_tower_of_forall_isPullback
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_section_forall_coe_one_comp_eq_of_tower_of_forall_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/eb8620cc-e50d-57f3-9098-60dc1f56024a
-- title:
--   Algebraising the unit sections of a formal fake elliptic curve
-- statement:
--   Let $q\neq q'$ be primes and $a,b\in\mathbb{Q}$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0<a$ or $0<b$) and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order (containing $1$, closed under multiplication, spanning over $\mathbb{Q}$, finitely generated) and maximal among orders; let $\mu\in\Lambda$ satisfy $\mu^2=-(qq')\cdot 1$ and let $\mathrm{star}:\Lambda\to\Lambda$ satisfy $\mu\,\mathrm{star}(x)=\bar{x}\mu$ for all $x\in\Lambda$. Let $R$ be a noetherian local ring, complete for the $\mathfrak{m}$-adic topology, and let $\pi_n:R/\mathfrak{m}^{n+2}\to R/\mathfrak{m}^{n+1}$ be ring maps compatible with the quotient maps from $R$. Let $E_n$ be a fake elliptic curve of level $1$ over $R/\mathfrak{m}^{n+1}$ with $\Lambda$-action, and $t_n:(E_n).A\to(E_{n+1}).A$ morphisms exhibiting $(E_n).A$ as the pullback of $(E_{n+1}).A$ along $\operatorname{Spec}\pi_n$, compatibly with the relative group laws, the $\Lambda$-actions and the level data. Let $Z$ be a scheme with a finite morphism $G$ to $\mathbb{P}^r_R=\operatorname{Proj}$ of the homogeneous subalgebra of $R[x_0,\dots,x_r]$, and let $j_n:(E_n).A\to Z$ satisfy $t_n$ followed by $j_{n+1}$ equals $j_n$ and exhibit each $(E_n).A$ as the fibre product of $Z\to\operatorname{Spec}R$ (via $G$ followed by the structural projection $\pi$) with $\operatorname{Spec}(R/\mathfrak{m}^{n+1})\to\operatorname{Spec}R$. Then there exists $e:\operatorname{Spec}R\to Z$ which is a section of $Z\to\operatorname{Spec}R$, that is $e$ followed by $G$ followed by $\pi$ is the identity, and which restricts to every unit section: for all $n$, every scheme $T$ and every $t':T\to\operatorname{Spec}(R/\mathfrak{m}^{n+1})$, the unit $(E_n).L.\mathrm{one}\,t'$ followed by $j_n$ equals $t'$ followed by $\operatorname{Spec}$ of the quotient map $R\to R/\mathfrak{m}^{n+1}$, followed by $e$.
--
--   This is the formal-geometry algebraisation step in the Čerednik–Drinfeld construction: the compatible system of unit sections of a tower of fake elliptic curves over the truncations $R/\mathfrak{m}^{n+1}$ comes from a single section of the ambient scheme $Z$, which is available because $Z$ is finite over a projective space over the complete ring $R$. It feeds the construction of the group-law data on the algebraised object, in [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_mul_unit_inv_act_hom_forall_comp_eq_of_tower_of_forall_isPullback`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_mul_unit_inv_act_hom_forall_comp_eq_of_tower_of_forall_isPullback).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_section_forall_coe_one_comp_eq_of_tower_of_forall_isPullback.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_section_forall_coe_one_comp_eq_of_tower_of_forall_isPullback
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
    ∃ (e : Spec (CommRingCat.of R) ⟶ Z) (he : e ≫ (G ≫ ProjSpace.π R r) = 𝟙 _),
      (∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))),
        ((E n).L.one t').1 ≫ jz n = (t' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))))) ≫ e) := by sorry
