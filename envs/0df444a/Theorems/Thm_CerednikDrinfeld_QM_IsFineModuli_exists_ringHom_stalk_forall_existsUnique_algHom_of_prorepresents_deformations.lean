-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_exists_ringHom_stalk_forall_existsUnique_algHom_of_prorepresents_deformations
-- name    : CerednikDrinfeld.QM.IsFineModuli.exists_ringHom_stalk_forall_existsUnique_algHom_of_prorepresents_deformations
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/67456efd-0a75-5ad4-89db-b54f690e2ad3
-- title:
--   Pro-representing the stalk via the special formal module
-- statement:
--   Fix distinct primes $q,q'$ and rationals $a,b$ such that $\mathbb H[\mathbb Q,a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'` (namely $0<a$ or $0<b$, and a height-one prime $v$ of $\mathbb Q$ has $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ a division algebra exactly when $v$ lies over $q$ or over $q'$). Let $\Lambda$ be a maximal order in it (an order that is maximal among the orders containing it), let $m\ge 3$ with $q\nmid m$, and let $\mathrm{coord}:\Lambda\to \mathbb Z_{q^2}\times\mathbb Z_{q^2}$ (Witt vectors of $\mathbb F_{q^2}$) satisfy `IsOrderCoord`: additive, injective, $1\mapsto(1,0)$, multiplicative for the twisted rule with Frobenius and $q$, dense modulo every power of $q$, and compatible with reduced traces. Let $\pi_M:M\to\operatorname{Spec}\mathbb Z_{q}$ together with $\mathrm{ptF}$ be a fine moduli scheme for fake elliptic curves over $\Lambda$ with level $N=1$ and full level $m$ (so $\mathrm{ptF}$ is constant on isomorphism classes, compatible with base change, surjective, and injective up to isomorphism), and let $y\in M$. Let $O$ be a local $\mathbb Z_q$-algebra with $q$ in the maximal ideal and algebraically closed residue field, $\iota:\mathbb Z_{q^2}\to O$ a ring homomorphism, and $\bar x:\mathcal O_{M,y}\to \mathrm{ResidueField}\,O$ a ring homomorphism whose kernel is the maximal ideal. Let $u_0$ be a fake elliptic curve with full level $m$ over $\mathrm{ResidueField}\,O$ whose associated point $\mathrm{ptF}$, over the structure map induced by $O\to\mathrm{ResidueField}\,O$, is $\operatorname{Spec}\bar x$ followed by $M.\mathrm{fromSpecStalk}\,y$; let $X_0$ be a formal $\mathcal O_D$-module over $\mathrm{ResidueField}\,O$, special for $(\mathrm{residue}\,O)\circ\iota$ and of height $4$, and $\theta_0$ a two-dimensional system of formal coordinates along $u_0.1.f$ with `IsFormalModuleVia coord`, identifying the relative group law's infinitesimal points with $X_0$ and the $\Lambda$-action with the action through $\mathrm{coord}$. Let $R$ be a noetherian local $O$-algebra, complete for its maximal ideal, with residue map $\mathrm{res}_R$ lifting $\mathrm{residue}\,O$, and let $X^u$ be a formal $\mathcal O_D$-module over $R$ with an isomorphism $w^u:X^u\otimes_R\mathrm{ResidueField}\,O\to X_0$. Assume $(R,X^u,w^u)$ pro-represents the deformation problem: for every Artin local $O$-algebra $A$ with surjective residue map $\mathrm{res}_A$ lifting $\mathrm{residue}\,O$, every formal $\mathcal O_D$-module $X$ over $A$ that is special for $(\mathrm{algebraMap}\,O\,A)\circ\iota$ and of height $4$, and every isomorphism $w$ from the reduction of $X$ to $X_0$, there is a unique $O$-algebra map $\chi:R\to A$ with $\mathrm{res}_A\circ\chi=\mathrm{res}_R$ admitting an isomorphism $v:X^u\otimes_R A\to X$ whose reduction composed with $w$ has the same power series as $w^u$. Then there is a ring homomorphism $\varphi:\mathcal O_{M,y}\to R$ with $\mathrm{res}_R\circ\varphi=\bar x$ such that for every Artin local $O$-algebra $A$ with surjective residue map $\mathrm{res}_A$ lifting $\mathrm{residue}\,O$ and every ring homomorphism $\psi:\mathcal O_{M,y}\to A$ with $\mathrm{res}_A\circ\psi=\bar x$, there is a unique $O$-algebra homomorphism $\chi:R\to A$ with $\mathrm{res}_A\circ\chi=\mathrm{res}_R$ and $\chi\circ\varphi=\psi$.
--
--   This is the Serre–Tate transfer in the Čerednik–Drinfel'd setting: the deformation theory of the special formal $\mathcal O_D$-module attached to the fibre at a geometric point is carried over to the local ring of the fine moduli scheme of fake elliptic curves, so that a ring pro-representing the one problem pro-represents the other. It feeds the identification of the complete local rings of the moduli scheme, being used to deduce that the stalk at a closed point is pro-represented by a regular local ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_exists_ringHom_stalk_forall_existsUnique_algHom_of_prorepresents_deformations.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing

theorem CerednikDrinfeld.QM.IsFineModuli.exists_ringHom_stalk_forall_existsUnique_algHom_of_prorepresents_deformations
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (m : ℕ) (hm : 3 ≤ m) (hqm : ¬ q ∣ m)
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of ℤ_[q]))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of ℤ_[q])),
      FakeEllipticCurve.WithFullLevel Λ 1 m S → SchemeHomOver s πM)
    (hM : IsFineModuli Λ 1 m M πM ptF)
    (y : M)

    (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[q] O]
    (hqO : algebraMap ℤ_[q] O (q : ℤ_[q]) ∈ maximalIdeal O) [IsAlgClosed (ResidueField O)]
    (ι : Zp2 q →+* O)

    (xbar : M.presheaf.stalk y →+* ResidueField O)
    (hxbar : RingHom.ker xbar = maximalIdeal (M.presheaf.stalk y))

    (u₀ : FakeEllipticCurve.WithFullLevel Λ 1 m (ResidueField O))
    (hu₀ : (ptF (ResidueField O) (Spec.map (CommRingCat.ofHom ((residue O).comp (algebraMap ℤ_[q] O)))) u₀).1 =
      Spec.map (CommRingCat.ofHom xbar) ≫ M.fromSpecStalk y)
    (X₀ : SpecialFormalODModule q ((residue O).comp ι))
    (θ₀ : RelativeGroupLaw.FormalCoordinates u₀.1.f 2)
    (hX₀ : u₀.1.IsFormalModuleVia coord X₀.toFormalODModule θ₀)

    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra O R]
    [IsAdicComplete (maximalIdeal R) R]
    (resR : R →+* ResidueField O) (hresR : resR.comp (algebraMap O R) = residue O)
    (Xu : FormalODModule q R) (wu : (Xu.map resR).Hom X₀.toFormalODModule) (hwu : wu.IsIso)
    (hPRO : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O), Function.Surjective resA →
        resA.comp (algebraMap O A) = residue O →
      ∀ (X : FormalODModule q A), X.IsSpecial ((algebraMap O A).comp ι) → X.HasHeight 4 →
      ∀ (w : (X.map resA).Hom X₀.toFormalODModule), w.IsIso →
        ∃! χ : R →ₐ[O] A, resA.comp χ.toRingHom = resR ∧
          ∃ v : (Xu.map χ.toRingHom).Hom X, v.IsIso ∧
            (w.comp (v.map resA)).toSeries = wu.toSeries) :
    ∃ φ : M.presheaf.stalk y →+* R, resR.comp φ = xbar ∧
      ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
          (resA : A →+* ResidueField O), Function.Surjective resA →
          resA.comp (algebraMap O A) = residue O →
        ∀ ψ : M.presheaf.stalk y →+* A, resA.comp ψ = xbar →
          ∃! χ : R →ₐ[O] A, resA.comp χ.toRingHom = resR ∧ χ.toRingHom.comp φ = ψ := by sorry
