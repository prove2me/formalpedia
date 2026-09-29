-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_exists_withFullLevel_isPullbackVia_ptF_eq_of_ringHom_stalk
-- name    : CerednikDrinfeld.QM.IsFineModuli.exists_withFullLevel_isPullbackVia_ptF_eq_of_ringHom_stalk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/176bf297-30ba-5668-9cc4-c7b9a242552b
-- title:
--   Curves over Artin local rings from points of the fine moduli scheme
-- statement:
--   Fix distinct primes $q\neq q'$ and rationals $a,b$ such that $\mathbb H[\mathbb Q,a,b]$ is indefinite ($0<a$ or $0<b$) and, for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$, the completion $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ be a $\mathbb Z$-submodule which is a maximal order (an order: contains $1$, closed under multiplication, $\mathbb Q$-spanning, finitely generated; and maximal among orders containing it), and let $m\geq 3$ with $q\nmid m$. Let $\pi_M\colon M\to\operatorname{Spec}\mathbb Z_q$ be a scheme over $\mathbb Z_q$ together with an assignment `ptF` sending a commutative ring $S$, a morphism $s\colon\operatorname{Spec}S\to\operatorname{Spec}\mathbb Z_q$ and a fake elliptic curve over $S$ for $\Lambda$ of level $1$ equipped with a full level-$m$ structure to a morphism $\operatorname{Spec}S\to M$ over $s$, and assume `IsFineModuli`: `ptF` is constant on isomorphism classes, compatible with base change along ring maps that are pullbacks of the curve data, surjective onto morphisms over $s$, and injective up to isomorphism. Let $y\in M$, let $O$ be a local $\mathbb Z_q$-algebra with the image of $q$ in its maximal ideal and algebraically closed residue field, and let $\bar x\colon\mathcal O_{M,y}\to\operatorname{ResidueField}O$ be a ring map with kernel the maximal ideal of the stalk. Let $u_0$ be a fake elliptic curve with full level $m$ over $\operatorname{ResidueField}O$ whose classifying morphism over $\operatorname{Spec}$ of $\mathrm{residue}_O\circ(\mathbb Z_q\to O)$ equals $\operatorname{Spec}\bar x$ followed by $M.\mathrm{fromSpecStalk}\,y$. Finally let $A$ be an Artinian local $O$-algebra with a surjection $\mathrm{res}_A\colon A\to\operatorname{ResidueField}O$ satisfying $\mathrm{res}_A\circ(O\to A)=\mathrm{residue}_O$, and let $\psi\colon\mathcal O_{M,y}\to A$ satisfy $\mathrm{res}_A\circ\psi=\bar x$. Then there are a fake elliptic curve with full level $m$ over $A$, say $u$, and a morphism $g\colon u_0$'s abelian scheme $\to u$'s abelian scheme such that: the square formed by $g$, the two structure morphisms and $\operatorname{Spec}\mathrm{res}_A$ is a pullback, $g$ is compatible with the relative group laws on points, commutes with the $\Lambda$-actions, and carries points factoring through the level morphism of $u_0$ to points factoring through that of $u$; the level-$m$ section of $u_0$ followed by $g$ equals $\operatorname{Spec}\mathrm{res}_A$ followed by the level-$m$ section of $u$; and the classifying morphism of $u$ over $\operatorname{Spec}$ of $(O\to A)\circ(\mathbb Z_q\to O)$ equals $\operatorname{Spec}\psi$ followed by $M.\mathrm{fromSpecStalk}\,y$.
--
--   This is the deformation-theoretic reading of the fine moduli property: a ring map from the local ring at a point $y$ of the moduli scheme to an Artin local ring with residue field $\bar k$ is realised by a fake elliptic curve with full level-$m$ structure over that Artin local ring whose reduction is the curve classified by the geometric point, together with the comparison isomorphism of the reduction. It feeds the comparison of the local ring at $y$ with the universal deformation ring of the associated formal module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_exists_withFullLevel_isPullbackVia_ptF_eq_of_ringHom_stalk.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  IsLocalRing

theorem CerednikDrinfeld.QM.IsFineModuli.exists_withFullLevel_isPullbackVia_ptF_eq_of_ringHom_stalk
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
    (ψ : M.presheaf.stalk y →+* A) (hψ : resA.comp ψ = xbar) :
    ∃ (u : FakeEllipticCurve.WithFullLevel Λ 1 m A) (g : u₀.1.A ⟶ u.1.A),
      FakeEllipticCurve.IsPullbackVia resA u.1 u₀.1 g ∧
      (u₀.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom resA) ≫ (u.2.P).1 ∧
      (ptF A (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp (algebraMap ℤ_[q] O)))) u).1 = (Spec.map (CommRingCat.ofHom ψ) ≫ M.fromSpecStalk y) := by sorry
