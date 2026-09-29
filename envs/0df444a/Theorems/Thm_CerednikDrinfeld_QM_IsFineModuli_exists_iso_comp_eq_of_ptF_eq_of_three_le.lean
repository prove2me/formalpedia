-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_exists_iso_comp_eq_of_ptF_eq_of_three_le
-- name    : CerednikDrinfeld.QM.IsFineModuli.exists_iso_comp_eq_of_ptF_eq_of_three_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/6b5e0c59-b389-55cd-b947-75bc22b20e3d
-- title:
--   Rigidity of level-m moduli points over an Artinian base
-- statement:
--   Fix distinct primes $q,q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0<a$ or $0<b$) and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $v$ lies over $q$ or $q'$; let $\Lambda$ be a maximal order, i.e. a $\mathbb{Z}$-submodule containing $1$, closed under multiplication, finitely generated, spanning the algebra over $\mathbb{Q}$, and maximal among such, and let $m\ge 3$ with $q\nmid m$. Let $\pi_M\colon M\to \operatorname{Spec}\mathbb{Z}_q$ together with the assignment `ptF`, sending each ring $S$, each $s\colon \operatorname{Spec}S\to\operatorname{Spec}\mathbb{Z}_q$ and each fake elliptic curve over $S$ with level $1$ and full level-$m$ structure to a morphism $\operatorname{Spec}S\to M$ over $s$, satisfy `IsFineModuli` (invariance under isomorphism, compatibility with pullbacks, surjectivity, and injectivity up to isomorphism), and let $y\in M$. Let $O$ be a local $\mathbb{Z}_q$-algebra in which $q$ lies in the maximal ideal and whose residue field is algebraically closed, and let $\bar x\colon \mathcal{O}_{M,y}\to \operatorname{ResidueField}O$ be a ring homomorphism with kernel the maximal ideal. Let $u_0$ be such a curve over $\operatorname{ResidueField}O$ whose moduli morphism, taken over the map induced by $O\to\operatorname{ResidueField}O$ composed with $\mathbb{Z}_q\to O$, equals $\operatorname{Spec}(\bar x)$ followed by $M.\mathrm{fromSpecStalk}\,y$. Let $A$ be an Artinian local $O$-algebra with a surjective ring homomorphism $\mathrm{res}_A\colon A\to\operatorname{ResidueField}O$ compatible with the residue map of $O$, and let $u,u'$ be curves of the same kind over $A$ together with $g\colon u_0.A\to u.A$ and $g'\colon u_0.A\to u'.A$ each exhibiting $u_0$ as the pullback along $\operatorname{Spec}(\mathrm{res}_A)$ in the sense of `IsPullbackVia` (cartesian square, compatibility with the relative group laws and with the $\Lambda$-actions, and descent of points factoring through the level morphism), and each carrying the level-$m$ section of $u_0$ to the base change of that of $u$, resp. $u'$. Assume the two moduli morphisms of $u$ and $u'$ over $\operatorname{Spec}A\to\operatorname{Spec}\mathbb{Z}_q$ coincide. Then there is an isomorphism of schemes $e\colon u.A\cong u'.A$ with $g$ followed by $e$ equal to $g'$, such that $e$ is a morphism over $A$ and, as such, is a homomorphism for the relative group laws on all $T$-points and commutes with the action of every $x\in\Lambda$. No compatibility of $e$ with the level-$m$ sections is asserted.
--
--   This is the rigidity step in the deformation-theoretic analysis of the fine moduli scheme of fake elliptic curves with full level-$m$ structure: equality of moduli points over an Artinian local base yields an isomorphism that is not merely abstract but compatible with the prescribed reductions to the fixed geometric fibre. It is used in establishing that the stalk of the moduli scheme pro-represents the associated deformation functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_exists_iso_comp_eq_of_ptF_eq_of_three_le.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  IsLocalRing

theorem CerednikDrinfeld.QM.IsFineModuli.exists_iso_comp_eq_of_ptF_eq_of_three_le
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (m : ℕ) (hm : 3 ≤ m) (hqm : ¬ q ∣ m)
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of ℤ_[q]))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of ℤ_[q])),
      FakeEllipticCurve.WithFullLevel Λ 1 m S → SchemeHomOver s πM)
    (hM : IsFineModuli Λ 1 m M πM ptF)
    (y : M)

    (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[q] O]
    (hqO : algebraMap ℤ_[q] O (q : ℤ_[q]) ∈ maximalIdeal O) [IsAlgClosed (ResidueField O)]

    (xbar : M.presheaf.stalk y →+* ResidueField O)
    (hxbar : RingHom.ker xbar = maximalIdeal (M.presheaf.stalk y))

    (u₀ : FakeEllipticCurve.WithFullLevel Λ 1 m (ResidueField O))
    (hu₀ : (ptF (ResidueField O) (Spec.map (CommRingCat.ofHom ((residue O).comp (algebraMap ℤ_[q] O)))) u₀).1 =
      Spec.map (CommRingCat.ofHom xbar) ≫ M.fromSpecStalk y)

    (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
    (resA : A →+* ResidueField O) (hs : Function.Surjective resA) (hc : resA.comp (algebraMap O A) = residue O)
    (u u' : FakeEllipticCurve.WithFullLevel Λ 1 m A) (g : u₀.1.A ⟶ u.1.A) (g' : u₀.1.A ⟶ u'.1.A)
    (hg : FakeEllipticCurve.IsPullbackVia resA u.1 u₀.1 g) (hP : (u₀.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom resA) ≫ (u.2.P).1)
    (hg' : FakeEllipticCurve.IsPullbackVia resA u'.1 u₀.1 g') (hP' : (u₀.2.P).1 ≫ g' = Spec.map (CommRingCat.ofHom resA) ≫ (u'.2.P).1)
    (hpt : (ptF A (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp (algebraMap ℤ_[q] O)))) u).1 = (ptF A (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp (algebraMap ℤ_[q] O)))) u').1) :
    ∃ e : u.1.A ≅ u'.1.A, g ≫ e.hom = g' ∧
      ∃ he : e.hom ≫ u'.1.f = u.1.f,
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of A)) (P Q : SchemeHomOver t u.1.f),
          mapPt e.hom he (u.1.L.mul t P Q) = u'.1.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
        (∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ u'.1.act x) := by sorry
