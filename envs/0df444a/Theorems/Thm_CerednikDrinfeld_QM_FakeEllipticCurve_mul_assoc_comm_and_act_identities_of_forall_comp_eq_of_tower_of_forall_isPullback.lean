-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_mul_assoc_comm_and_act_identities_of_forall_comp_eq_of_tower_of_forall_isPullback
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.mul_assoc_comm_and_act_identities_of_forall_comp_eq_of_tower_of_forall_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/beb88242-c674-5188-b670-238d16b3736d
-- title:
--   Group law and Λ-action identities on the algebraised model
-- statement:
--   Fix distinct primes $q,q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0<a$ or $0<b$) and the finite places at which it is a division algebra are exactly those above $q$ or $q'$; let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a maximal order (an order — containing $1$, multiplicatively closed, $\mathbb{Q}$-spanning, finitely generated — maximal among orders), $\mu\in\Lambda$ with $\mu^2=-(qq')\cdot 1$, and $\mathrm{star}:\Lambda\to\Lambda$ with $\mu\,\mathrm{star}(x)=\bar{x}\mu$. Let $R$ be a noetherian local ring, complete for its maximal ideal $\mathfrak m$, with transition maps $\pi_n:R/\mathfrak m^{n+2}\to R/\mathfrak m^{n+1}$ compatible with the quotient maps. Let $(E_n)$ be level-$1$ fake elliptic curves for $\Lambda$ over $R/\mathfrak m^{n+1}$ and $t_n:A_n\to A_{n+1}$ exhibiting $A_n$ as the pullback of $A_{n+1}$ along $\mathrm{Spec}\,\pi_n$, compatibly with group laws, $\Lambda$-actions and level structures. Let $Z$ be a scheme with a finite morphism $G$ to $\mathbb{P}^r_R$; put $f_Z=G$ followed by the structure map, and let $j_n:A_n\to Z$ satisfy $t_n$ followed by $j_{n+1}$ equals $j_n$ and exhibit each square over $\mathrm{Spec}\,R/\mathfrak m^{n+1}$ as a pullback. Given $m:Z\times_{f_Z}Z\to Z$, a section $e$ of $f_Z$, $\iota:Z\to Z$ and $\mathrm{act}(x):Z\to Z$ ($x\in\Lambda$), all over $f_Z$, which restrict along every $j_n$ to the multiplication, unit, inversion and $\Lambda$-action of $E_n$ on $T$-points, the conclusion asserts: on $T$-points of $Z$ over $\mathrm{Spec}\,R$, $m$ is associative and commutative with two-sided unit $t'\!\circ\! e$ and inversion $\iota$; and $\mathrm{act}\langle 1\rangle=\mathbb{1}_Z$, $\mathrm{act}(xy)=\mathrm{act}(y)$ followed by $\mathrm{act}(x)$, each $\mathrm{act}(x)$ is an endomorphism for $m$, and $P\circ\mathrm{act}(x+y)=m(P\circ\mathrm{act}(x),P\circ\mathrm{act}(y))$.
--
--   This is the verification step in the algebraisation of a tower of fake elliptic curves over the truncations $R/\mathfrak m^{n+1}$ of a complete noetherian local ring: once the multiplication, unit, inversion and quaternionic action have been produced on the algebraised scheme $Z$, their identities are inherited from the corresponding identities on each $E_n$. It is used by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_mul_unit_inv_act_hom_forall_comp_eq_of_tower_of_forall_isPullback`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_mul_unit_inv_act_hom_forall_comp_eq_of_tower_of_forall_isPullback), which assembles the group data on $Z$ into a fake elliptic curve over $R$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_mul_assoc_comm_and_act_identities_of_forall_comp_eq_of_tower_of_forall_isPullback.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.mul_assoc_comm_and_act_identities_of_forall_comp_eq_of_tower_of_forall_isPullback
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
      (∀ n, CategoryTheory.IsPullback (jz n) (E n).f (G ≫ ProjSpace.π R r) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))))
    (m : pullback (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ⟶ Z) (hm : m ≫ (G ≫ ProjSpace.π R r) = pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r))
    (e : Spec (CommRingCat.of R) ⟶ Z) (he : e ≫ (G ≫ ProjSpace.π R r) = 𝟙 _)
    (ι : Z ⟶ Z) (hι : ι ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r)) (act : ↥Λ → (Z ⟶ Z)) (act_over : ∀ x : ↥Λ, act x ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r))
    (hmul : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P Q : SchemeHomOver t' (E n).f),
        ((E n).L.mul t' P Q).1 ≫ jz n =
          pullback.lift (P.1 ≫ jz n) (Q.1 ≫ jz n)
            (by simp only [Category.assoc]; rw [(hZ.2 n).w, ← Category.assoc, P.2, ← Category.assoc, Q.2]) ≫ m)
    (hone : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))),
        ((E n).L.one t').1 ≫ jz n = (t' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))))) ≫ e)
    (hinv : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P : SchemeHomOver t' (E n).f),
        ((E n).L.inv t' P).1 ≫ jz n = (P.1 ≫ jz n) ≫ ι)
    (hact : ∀ (n : ℕ) (x : ↥Λ), (E n).act x ≫ jz n = jz n ≫ act x)
 :
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
          pullback.lift (P.1 ≫ act x) (P.1 ≫ act y) (by rw [Category.assoc, act_over, Category.assoc, act_over]) ≫ m) := by sorry
