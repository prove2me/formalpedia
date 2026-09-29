-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_mul_unit_inv_act_hom_forall_comp_eq_of_tower_of_forall_isPullback
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_mul_unit_inv_act_hom_forall_comp_eq_of_tower_of_forall_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/3783b753-f8c6-5041-8840-1b2cf4cd993b
-- title:
--   Algebraisation of group law and Λ-action over the tower
-- statement:
--   Let $q\neq q'$ be primes, let $a,b\in\mathbb{Q}$ be such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds, i.e. $a>0$ or $b>0$ and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is a maximal order (an order: it contains $1$, is multiplicatively closed, $\mathbb{Q}$-spans the algebra and is finitely generated; and is maximal among such), let $\mu\in\Lambda$ satisfy $\mu^2=-(qq')\cdot 1$ and let $\mathrm{star}:\Lambda\to\Lambda$ satisfy $\mu\cdot\mathrm{star}(x)=\bar{x}\mu$ for all $x\in\Lambda$. Let $R$ be a noetherian local ring, complete for the $\mathfrak{m}$-adic topology, with transition maps $\pi_n:R/\mathfrak{m}^{n+2}\to R/\mathfrak{m}^{n+1}$ compatible with the quotient maps. Let $E_n$ be a fake elliptic curve over $R/\mathfrak{m}^{n+1}$ with $\Lambda$-action and level datum of level $1$, and let $t_n:(E_n).A\to(E_{n+1}).A$ satisfy `IsPullbackVia (π n)`: the square with $(E_n).f$, $(E_{n+1}).f$ and $\operatorname{Spec}(\pi_n)$ is a pullback, $t_n$ carries the relative group law of $E_n$ to that of $E_{n+1}$ on $T$-points, commutes with the $\Lambda$-actions, and sends points factoring through $(E_n).\mathrm{lev}$ to points factoring through $(E_{n+1}).\mathrm{lev}$. Finally let $Z$ be a scheme with a finite morphism $G$ to $\mathbb{P}^r_R=\mathrm{Proj}$ of the homogeneous polynomial algebra in $r+1$ variables over $R$, write $f_Z=G\mathbin{;}\mathrm{ProjSpace}.\pi\,R\,r$ for the resulting morphism to $\operatorname{Spec}R$, and let $j_n:(E_n).A\to Z$ satisfy $t_n$ followed by $j_{n+1}$ equals $j_n$, each square $(j_n,(E_n).f,f_Z,\operatorname{Spec}(R\to R/\mathfrak{m}^{n+1}))$ being a pullback. The conclusion asserts the existence of $m:Z\times_{\operatorname{Spec}R}Z\to Z$, a section $e:\operatorname{Spec}R\to Z$, an involution candidate $\iota:Z\to Z$ and maps $\rho(x):Z\to Z$ for $x\in\Lambda$, all compatible with $f_Z$ ($m$ followed by $f_Z$ equals the first projection followed by $f_Z$; $e$ followed by $f_Z$ is the identity; $\iota$ and each $\rho(x)$ followed by $f_Z$ equal $f_Z$), such that on $T$-points over $\operatorname{Spec}R$ (pairs of a morphism $T\to Z$ with prescribed composite to $\operatorname{Spec}R$) the law $m$ is associative, commutative, has $e$ as two-sided unit and $\iota$ as inverse; $\rho(1)=\mathrm{id}_Z$ when $1\in\Lambda$, $\rho(xy)=\rho(y)$ followed by $\rho(x)$, each $\rho(x)$ is a homomorphism for $m$, and $\rho(x+y)$ applied to a point is the $m$-product of $\rho(x)$ and $\rho(y)$ applied to it; and for every $n$ the morphism $j_n$ transports the multiplication, unit, inverse and $\Lambda$-action of $E_n$ into $m$, $e$, $\iota$ and $\rho$.
--
--   This is the algebraisation step of the Čerednik–Drinfeld uniformisation package for quaternionic (fake elliptic) curves: a compatible tower of level-$1$ fake elliptic curves over the truncations $R/\mathfrak{m}^{n+1}$, realised as the truncations of a single scheme $Z$ finite over $\mathbb{P}^r_R$, carries a group law, unit, inversion and $\Lambda$-action on $Z$ itself, restricting levelwise to those of the $E_n$. It is the structural input to [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_fakeEllipticCurve_forall_isPullbackVia_of_tower_of_forall_isPullback`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_fakeEllipticCurve_forall_isPullbackVia_of_tower_of_forall_isPullback), which assembles these data into a fake elliptic curve over $R$ whose truncations are the $E_n$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_mul_unit_inv_act_hom_forall_comp_eq_of_tower_of_forall_isPullback.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_mul_unit_inv_act_hom_forall_comp_eq_of_tower_of_forall_isPullback
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
    ∃ (m : pullback (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ⟶ Z) (e : Spec (CommRingCat.of R) ⟶ Z) (ι : Z ⟶ Z) (act : ↥Λ → (Z ⟶ Z))
      (hm : m ≫ (G ≫ ProjSpace.π R r) = pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (he : e ≫ (G ≫ ProjSpace.π R r) = 𝟙 _) (hι : ι ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r))
      (act_over : ∀ x : ↥Λ, act x ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r)),

      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R)) (x y z : SchemeHomOver t' (G ≫ ProjSpace.π R r)),
        pullback.lift (pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m) z.1
            (by rw [Category.assoc, hm, pullback.lift_fst_assoc, x.2, z.2]) ≫ m =
          pullback.lift x.1 (pullback.lift y.1 z.1 (y.2.trans z.2.symm) ≫ m)
            (by rw [Category.assoc, hm, pullback.lift_fst_assoc, y.2, x.2]) ≫ m) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t' (G ≫ ProjSpace.π R r)),
        pullback.lift (t' ≫ e) x.1 (by rw [Category.assoc, he, Category.comp_id, x.2]) ≫ m = x.1) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t' (G ≫ ProjSpace.π R r)),
        pullback.lift x.1 (t' ≫ e) (by rw [Category.assoc, he, Category.comp_id, x.2]) ≫ m = x.1) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t' (G ≫ ProjSpace.π R r)),
        pullback.lift (x.1 ≫ ι) x.1 (by rw [Category.assoc, hι]) ≫ m = t' ≫ e) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t' (G ≫ ProjSpace.π R r)),
        pullback.lift y.1 x.1 (y.2.trans x.2.symm) ≫ m = pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m) ∧

      (∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h1⟩ = 𝟙 Z) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ), act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x) ∧
      (∀ (x : ↥Λ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t' (G ≫ ProjSpace.π R r)),
        pullback.lift (P.1 ≫ act x) (Q.1 ≫ act x) (by rw [Category.assoc, act_over, Category.assoc, act_over, P.2, Q.2]) ≫ m =
          (pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) ≫ m) ≫ act x) ∧
      (∀ (x y : ↥Λ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t' (G ≫ ProjSpace.π R r)),
        P.1 ≫ act (x + y) =
          pullback.lift (P.1 ≫ act x) (P.1 ≫ act y) (by rw [Category.assoc, act_over, Category.assoc, act_over]) ≫ m) ∧

      (∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P Q : SchemeHomOver t' (E n).f),
        ((E n).L.mul t' P Q).1 ≫ jz n =
          pullback.lift (P.1 ≫ jz n) (Q.1 ≫ jz n)
            (by simp only [Category.assoc]; rw [(hZ.2 n).w, ← Category.assoc, P.2, ← Category.assoc, Q.2]) ≫ m) ∧
      (∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))),
        ((E n).L.one t').1 ≫ jz n = (t' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))))) ≫ e) ∧
      (∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P : SchemeHomOver t' (E n).f),
        ((E n).L.inv t' P).1 ≫ jz n = (P.1 ≫ jz n) ≫ ι) ∧
      (∀ (n : ℕ) (x : ↥Λ), (E n).act x ≫ jz n = jz n ≫ act x) := by sorry
