-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_mul_forall_coe_mul_comp_eq_lift_comp_of_tower_of_forall_isPullback
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_mul_forall_coe_mul_comp_eq_lift_comp_of_tower_of_forall_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/7a3d1506-014b-5a2e-8833-726cb029280d
-- title:
--   Algebraising the group law along a tower of fake elliptic curves
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$, and let $a,b\in\mathbb{Q}$ be such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds: $0<a$ or $0<b$, and for every height-one prime $v$ of the integers of $\mathbb{Q}$ the algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $q$ or $q'$ lies in $v$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is a maximal order (an order maximal among orders containing it), let $\mu\in\Lambda$ satisfy $\mu^2=-(qq')\cdot 1$, and let $\mathrm{star}:\Lambda\to\Lambda$ satisfy $\mu\,\mathrm{star}(x)=\bar{x}\mu$ for all $x\in\Lambda$. Let $R$ be a local noetherian commutative ring, complete for the $\mathfrak{m}$-adic topology, $\mathfrak{m}$ its maximal ideal, and let $\pi_n:R/\mathfrak{m}^{n+2}\to R/\mathfrak{m}^{n+1}$ be ring homomorphisms compatible with the quotient maps from $R$. Let $E_n$ be a `FakeEllipticCurve` for $\Lambda$ of level $1$ over $R/\mathfrak{m}^{n+1}$ and $t_n:(E_n).A\to (E_{n+1}).A$ morphisms with `IsPullbackVia` $(\pi_n)$: each $t_n$ makes $(E_n).A$ the fibre product of $(E_{n+1}).A$ with $\operatorname{Spec}(R/\mathfrak{m}^{n+1})$ over $\operatorname{Spec}(R/\mathfrak{m}^{n+2})$, and is compatible with the relative group laws, with the $\Lambda$-actions and with factorisation through the level structures. Let $r\in\mathbb{N}$, let $Z$ be a scheme and $G:Z\to \operatorname{Proj}$ of the homogeneous polynomials in $r+1$ variables over $R$ a finite morphism, and let $j_n:(E_n).A\to Z$ satisfy $t_n$ followed by $j_{n+1}$ equals $j_n$, and exhibit each square $(j_n,(E_n).f, G$ followed by `ProjSpace.π R r`, $\operatorname{Spec}$ of the quotient map$)$ as a pullback. Then there is a morphism $m$ from the fibre product of $G$ followed by `ProjSpace.π R r` with itself to $Z$, satisfying $m$ followed by that structure morphism equals `pullback.fst` followed by it, such that for every $n$, every scheme $T$, every $t':T\to\operatorname{Spec}(R/\mathfrak{m}^{n+1})$ and all $P,Q\in$ `SchemeHomOver t' (E n).f`, the product $(E_n).L.\mathrm{mul}\,t'\,P\,Q$ followed by $j_n$ equals the `pullback.lift` of ($P$ followed by $j_n$, $Q$ followed by $j_n$) followed by $m$.
--
--   This is the algebraisation, over a complete local noetherian base, of the group law carried by a compatible tower of level-one fake elliptic curves over the truncations $R/\mathfrak{m}^{n+1}$: the multiplications of the $E_n$, read through the identifications $j_n$, come from a single multiplication morphism $Z\times_{\operatorname{Spec} R}Z\to Z$ over $\operatorname{Spec} R$. It supplies the multiplication in [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_mul_unit_inv_act_hom_forall_comp_eq_of_tower_of_forall_isPullback`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_mul_unit_inv_act_hom_forall_comp_eq_of_tower_of_forall_isPullback), which assembles the full group data of the algebraised fake elliptic curve; the proof uses the finiteness of the fibre product over projective space and the algebraisation of morphisms of formal schemes finite over projective space.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_mul_forall_coe_mul_comp_eq_lift_comp_of_tower_of_forall_isPullback.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_mul_forall_coe_mul_comp_eq_lift_comp_of_tower_of_forall_isPullback
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
    ∃ (m : pullback (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ⟶ Z) (hm : m ≫ (G ≫ ProjSpace.π R r) = pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)),
      (∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P Q : SchemeHomOver t' (E n).f),
        ((E n).L.mul t' P Q).1 ≫ jz n =
          pullback.lift (P.1 ≫ jz n) (Q.1 ≫ jz n)
            (by simp only [Category.assoc]; rw [(hZ.2 n).w, ← Category.assoc, P.2, ← Category.assoc, Q.2]) ≫ m) := by sorry
