-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_exists_withFullLevel_isPullbackVia_comp_eq_ptF_eq_of_algHom
-- name    : CerednikDrinfeld.QM.IsFineModuli.exists_withFullLevel_isPullbackVia_comp_eq_ptF_eq_of_algHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/94c89534-d421-5b0f-a4f2-ec70519dc302
-- title:
--   Base change of a full-level fake elliptic curve along A → A'
-- statement:
--   Fix distinct primes $q,q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`: $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a maximal order (an order in the sense of containing $1$, closed under multiplication, $\mathbb{Q}$-spanning and finitely generated, maximal among such), $m\ge 3$ with $q\nmid m$, and let $\pi_M:M\to\operatorname{Spec}\mathbb{Z}_q$ together with $\mathrm{ptF}$, assigning to each ring $S$, each $s:\operatorname{Spec}S\to\operatorname{Spec}\mathbb{Z}_q$ and each pair $u$ of a fake elliptic curve for $(\Lambda,1)$ over $S$ with a full level-$m$ structure a morphism $\operatorname{Spec}S\to M$ over $s$, satisfy `IsFineModuli` (invariance under isomorphism, compatibility with pullbacks, surjectivity, and injectivity up to isomorphism). Let $y\in M$, let $O$ be a local $\mathbb{Z}_q$-algebra with $q$ in its maximal ideal and algebraically closed residue field, let $\bar x:\mathcal{O}_{M,y}\to\operatorname{ResidueField}O$ be a ring homomorphism with kernel the maximal ideal, and let $u_0$ be a fake elliptic curve with full level $m$ over $\operatorname{ResidueField}O$ whose moduli point over $\operatorname{Spec}$ of $\mathbb{Z}_q\to O\to\operatorname{ResidueField}O$ is $\operatorname{Spec}\bar x$ followed by $M.\mathrm{fromSpecStalk}\,y$. Let $A,A'$ be Artinian local $O$-algebras with surjections $\mathrm{res}_A,\mathrm{res}_{A'}$ onto $\operatorname{ResidueField}O$ compatible with the residue map of $O$, and $f:A\to A'$ an $O$-algebra map with $\mathrm{res}_{A'}\circ f=\mathrm{res}_A$. Let $u$ be a fake elliptic curve with full level $m$ over $A$, $g:u_0.A\to u.A$ such that $\mathrm{IsPullbackVia}\ \mathrm{res}_A$ holds (the square $g,u_0.f,u.f,\operatorname{Spec}\mathrm{res}_A$ is cartesian, $g$ is compatible with the relative group laws on points, intertwines the $\Lambda$-actions, and carries points factoring through $u_0$'s level morphism to points factoring through that of $u$), with $u_0$'s level section composed with $g$ equal to $\operatorname{Spec}\mathrm{res}_A$ followed by that of $u$, and let $\psi:\mathcal{O}_{M,y}\to A$ be such that the moduli point of $u$ over $\mathbb{Z}_q\to O\to A$ is $\operatorname{Spec}\psi$ followed by $M.\mathrm{fromSpecStalk}\,y$. Then there exist a fake elliptic curve with full level $m$ over $A'$, say $u'$, and morphisms $k:u'.A\to u.A$, $g':u_0.A\to u'.A$ such that $k$ exhibits $u'$ as pullback of $u$ via $f$ and $g'$ exhibits $u_0$ as pullback of $u'$ via $\mathrm{res}_{A'}$ (both in the above sense), $g'$ followed by $k$ equals $g$, the level section of $u_0$ composed with $g'$ equals $\operatorname{Spec}\mathrm{res}_{A'}$ followed by that of $u'$, and the moduli point of $u'$ over $\mathbb{Z}_q\to O\to A'$ is $\operatorname{Spec}(f\circ\psi)$ followed by $M.\mathrm{fromSpecStalk}\,y$.
--
--   This is the base-change step in the deformation-theoretic analysis of the fine moduli scheme of fake elliptic curves with full level $m$ structure over $\mathbb{Z}_q$: a deformation over $A$ together with its reduction to the residue field and its moduli point is transported along an $O$-algebra map $A\to A'$, all compatibilities being preserved. It feeds the construction showing that the local ring at $y$ pro-represents the deformation functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_exists_withFullLevel_isPullbackVia_comp_eq_ptF_eq_of_algHom.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  IsLocalRing

theorem CerednikDrinfeld.QM.IsFineModuli.exists_withFullLevel_isPullbackVia_comp_eq_ptF_eq_of_algHom
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
    (A' : Type) [CommRing A'] [IsLocalRing A'] [IsArtinianRing A'] [Algebra O A']
    (resA' : A' →+* ResidueField O) (hs' : Function.Surjective resA') (hc' : resA'.comp (algebraMap O A') = residue O)
    (f : A →ₐ[O] A') (hf : resA'.comp f.toRingHom = resA)
    (u : FakeEllipticCurve.WithFullLevel Λ 1 m A) (g : u₀.1.A ⟶ u.1.A)
    (hg : FakeEllipticCurve.IsPullbackVia resA u.1 u₀.1 g) (hP : (u₀.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom resA) ≫ (u.2.P).1)
    (ψ : M.presheaf.stalk y →+* A) (hpt : (ptF A (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp (algebraMap ℤ_[q] O)))) u).1 = (Spec.map (CommRingCat.ofHom ψ) ≫ M.fromSpecStalk y)) :
    ∃ (u' : FakeEllipticCurve.WithFullLevel Λ 1 m A') (k : u'.1.A ⟶ u.1.A) (g' : u₀.1.A ⟶ u'.1.A),
      FakeEllipticCurve.IsPullbackVia f.toRingHom u.1 u'.1 k ∧
      FakeEllipticCurve.IsPullbackVia resA' u'.1 u₀.1 g' ∧
      g' ≫ k = g ∧
      (u₀.2.P).1 ≫ g' = Spec.map (CommRingCat.ofHom resA') ≫ (u'.2.P).1 ∧
      (ptF A' (Spec.map (CommRingCat.ofHom ((algebraMap O A').comp (algebraMap ℤ_[q] O)))) u').1 = (Spec.map (CommRingCat.ofHom (f.toRingHom.comp ψ)) ≫ M.fromSpecStalk y) := by sorry
