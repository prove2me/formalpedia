-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_ptF_eq_of_iso_comp_eq
-- name    : CerednikDrinfeld.QM.IsFineModuli.ptF_eq_of_iso_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/69d28cbf-d5de-504f-8ead-15eaa93b224b
-- title:
--   Isomorphic level-m data over A give the same moduli point
-- statement:
--   Fix distinct primes $q,q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $a>0$ or $b>0$, and for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a maximal order (a finitely generated $\mathbb{Z}$-submodule containing $1$, closed under multiplication, $\mathbb{Q}$-spanning the algebra, and maximal among such), let $m\ge 3$ with $q\nmid m$, and let $\pi_M\colon M\to\operatorname{Spec}\mathbb{Z}_q$ together with the assignment `ptF`, sending a ring $S$, a morphism $s\colon\operatorname{Spec} S\to\operatorname{Spec}\mathbb{Z}_q$ and a fake elliptic curve over $S$ with full level-$m$ structure to a morphism $\operatorname{Spec} S\to M$ over $s$, satisfy `IsFineModuli Λ 1 m M πM ptF` (invariance under isomorphism, compatibility with pullback, surjectivity and injectivity of `ptF`). Let $y\in M$, let $O$ be a local $\mathbb{Z}_q$-algebra with the image of $q$ in its maximal ideal and algebraically closed residue field, let $\bar x$ be a ring map from the stalk at $y$ to $\operatorname{ResidueField} O$ with kernel the maximal ideal, and let $u_0$ be a fake elliptic curve with full level $m$ over $\operatorname{ResidueField} O$ whose moduli morphism along $\operatorname{residue}\circ(\mathbb{Z}_q\to O)$ equals $\operatorname{Spec}(\bar x)$ followed by $M.\mathrm{fromSpecStalk}\,y$. Let $A$ be an artinian local $O$-algebra with a surjection $\mathrm{res}_A\colon A\to\operatorname{ResidueField} O$ satisfying $\mathrm{res}_A\circ(O\to A)=\operatorname{residue} O$, and let $u,u'$ be fake elliptic curves with full level $m$ over $A$ equipped with morphisms $g,g'$ from the scheme underlying $u_0$ exhibiting $u_0$ as the pullback of $u$, resp. $u'$, along $\operatorname{Spec}(\mathrm{res}_A)$ compatibly with the group laws, the $\Lambda$-actions and the level-$1$ maps, and with $g$, $g'$ carrying the section of $u_0$ to the base changes of the sections of $u$, $u'$. Assume finally an isomorphism $e$ of the underlying schemes with $g$ followed by $e$ equal to $g'$, $e$ lying over $A$, compatible with the group laws and the $\Lambda$-actions, and with $P$ factoring through the level-$1$ map of $u$ if and only if its image under $e$ factors through that of $u'$. Then the morphisms $\operatorname{Spec} A\to M$ underlying $\mathrm{ptF}\,A\,s\,u$ and $\mathrm{ptF}\,A\,s\,u'$ coincide, where $s$ is induced by $O\to A$ composed with $\mathbb{Z}_q\to O$.
--
--   This is the isomorphism-invariance step in the Serre–Tate style comparison between the deformation functor of a fake elliptic curve with full level-$m$ structure and the local ring of the fine moduli scheme of the Shimura curve at a point: isomorphic deformations with matching reductions to $u_0$ are sent to the same $A$-valued point of $M$. It is used in the construction of the ring homomorphism out of the stalk at $y$ which pro-represents the deformation problem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_ptF_eq_of_iso_comp_eq.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  IsLocalRing

theorem CerednikDrinfeld.QM.IsFineModuli.ptF_eq_of_iso_comp_eq
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
    (e : u.1.A ≅ u'.1.A) (hge : g ≫ e.hom = g') (he : e.hom ≫ u'.1.f = u.1.f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of A)) (P Q : SchemeHomOver t u.1.f),
      mapPt e.hom he (u.1.L.mul t P Q) = u'.1.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    (hact : ∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ u'.1.act x)
    (hlev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of A)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.1.lev P ↔ FactorsThrough u'.1.lev (mapPt e.hom he P)) :
    (ptF A (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp (algebraMap ℤ_[q] O)))) u).1 = (ptF A (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp (algebraMap ℤ_[q] O)))) u').1 := by sorry
