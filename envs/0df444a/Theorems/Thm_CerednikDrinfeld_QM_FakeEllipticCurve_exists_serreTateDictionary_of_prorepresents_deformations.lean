-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_serreTateDictionary_of_prorepresents_deformations
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_serreTateDictionary_of_prorepresents_deformations
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/46f61052-82ef-535a-aa66-396addfdf43d
-- title:
--   Serre–Tate dictionary for deformations of a fake elliptic curve
-- statement:
--   Fix distinct primes $q,q'$ and rationals $a,b$ such that $\mathbb H[\mathbb Q,a,b]$ is indefinite ($0<a$ or $0<b$) and is a division algebra at exactly those places of $\mathbb Q$ lying over $q$ or $q'$; let $\Lambda\subset\mathbb H[\mathbb Q,a,b]$ be a maximal order (an order maximal among orders), $m\in\mathbb N$, and $\mathrm{coord}:\Lambda\to \mathbb Z_{q^2}\times\mathbb Z_{q^2}$ an order coordinatisation in the sense of `IsOrderCoord` (additive, sending $1$ to $(1,0)$, multiplicative for the Frobenius-twisted product rule, injective, with dense image modulo every $q^k$, and matching reduced traces). Let $O$ be a local $\mathbb Z_q$-algebra with $q$ in its maximal ideal and algebraically closed residue field, $\iota:\mathbb Z_{q^2}\to O$ a ring map, $u_0$ a fake elliptic curve over $\mathrm{ResidueField}\,O$ with $\Lambda$-action, level-$1$ datum and a full level-$m$ structure, $X_0$ a special formal $\mathcal O_D$-module of height $4$ over $\mathrm{ResidueField}\,O$ relative to $(\mathrm{residue}\,O)\circ\iota$, and $\theta_0$ formal coordinates of genus $2$ along the unit section of $u_0$ exhibiting $u_0$ as a formal module via $\mathrm{coord}$ with underlying module $X_0$. Let $R$ be a noetherian local $O$-algebra, complete for the maximal-ideal topology, with $\mathrm{res}_R:R\to\mathrm{ResidueField}\,O$ compatible with $\mathrm{residue}\,O$, and $X^u$ a formal $\mathcal O_D$-module over $R$ together with an isomorphism $w^u:X^u\otimes_R\mathrm{ResidueField}\,O\xrightarrow{\sim}X_0$. Assume `hPRO`: for every Artin local $O$-algebra $A$ with surjective residue map $\mathrm{res}_A$ compatible with $\mathrm{residue}\,O$, every formal $\mathcal O_D$-module $X$ over $A$ that is special for $(\mathrm{algebraMap}\,O\,A)\circ\iota$ and of height $4$, and every isomorphism $w:X\otimes_A\mathrm{ResidueField}\,O\xrightarrow{\sim}X_0$, there is a unique $O$-algebra map $\chi:R\to A$ with $\mathrm{res}_A\circ\chi=\mathrm{res}_R$ admitting an isomorphism $v:X^u\otimes_\chi A\xrightarrow{\sim}X$ whose reduction composed with $w$ has the same power series as $w^u$. Then there is a rule $\Phi$ assigning to each such $(A,\mathrm{res}_A)$ and each pair $(E,g)$, where $E$ is a fake elliptic curve of level $1$ over $A$ and $g:u_0.A\to E.A$ exhibits $u_0$'s underlying curve as the pullback of $E$ along $\mathrm{res}_A$ (a pullback square compatible with the group laws, the $\Lambda$-actions, and the level morphisms), an $O$-algebra map $\Phi_A(E,g):R\to A$ such that: $\mathrm{res}_A\circ\Phi_A(E,g)=\mathrm{res}_R$; if $\Phi_A(E,g)=\Phi_A(E',g')$ then there is an isomorphism $e:E.A\cong E'.A$ over $A$ with $g$ followed by $e$ equal to $g'$, compatible with the group laws, $\Lambda$-equivariant, and matching the two level conditions; conversely any such isomorphism over $A$ carrying $g$ to $g'$ and compatible with group laws and $\Lambda$-actions forces $\Phi_A(E,g)=\Phi_A(E',g')$; every $O$-algebra map $\chi:R\to A$ with $\mathrm{res}_A\circ\chi=\mathrm{res}_R$ is of the form $\Phi_A(E,g)$; and $\Phi$ is functorial: for an $O$-algebra map $f:A\to A'$ between Artin local $O$-algebras compatible with the residue maps and $k:E'.A\to E.A$ exhibiting $E'$ as the pullback of $E$ along $f$, one has $\Phi_{A'}(E',g')=f\circ\Phi_A(E,g'\text{ followed by }k)$.
--
--   This is the Serre–Tate dictionary in the Čerednik–Drinfeld setting: it transfers a pro-representability statement for deformations of the special formal $\mathcal O_D$-module $X_0$ of height $4$ to the deformation functor of the fake elliptic curve $u_0$, with $\Phi$ recording which Artinian deformation of the curve corresponds to which $O$-algebra map out of $R$. It is used in the construction of the ring homomorphism from the local ring of the fine moduli scheme, where the formal neighbourhood of a point of the Shimura curve in characteristic $q$ is identified with the deformation space of the associated special formal module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_serreTateDictionary_of_prorepresents_deformations.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_serreTateDictionary_of_prorepresents_deformations
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (m : ℕ)
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[q] O]
    (hqO : algebraMap ℤ_[q] O (q : ℤ_[q]) ∈ maximalIdeal O) [IsAlgClosed (ResidueField O)]
    (ι : Zp2 q →+* O)
    (u₀ : FakeEllipticCurve.WithFullLevel Λ 1 m (ResidueField O))
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
    ∃ Φ : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O), Function.Surjective resA → resA.comp (algebraMap O A) = residue O →
        ∀ (E : FakeEllipticCurve Λ 1 A) (g : u₀.1.A ⟶ E.A),
          FakeEllipticCurve.IsPullbackVia resA E u₀.1 g → (R →ₐ[O] A),

      (∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
          (resA : A →+* ResidueField O) (hs : Function.Surjective resA) (hc : resA.comp (algebraMap O A) = residue O)
          (E : FakeEllipticCurve Λ 1 A) (g : u₀.1.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia resA E u₀.1 g),
        resA.comp (Φ A resA hs hc E g hg).toRingHom = resR) ∧

      (∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
          (resA : A →+* ResidueField O) (hs : Function.Surjective resA) (hc : resA.comp (algebraMap O A) = residue O)
          (E E' : FakeEllipticCurve Λ 1 A) (g : u₀.1.A ⟶ E.A) (g' : u₀.1.A ⟶ E'.A)
          (hg : FakeEllipticCurve.IsPullbackVia resA E u₀.1 g) (hg' : FakeEllipticCurve.IsPullbackVia resA E' u₀.1 g'),
        Φ A resA hs hc E g hg = Φ A resA hs hc E' g' hg' →
        ∃ e : E.A ≅ E'.A, g ≫ e.hom = g' ∧
          ∃ he : e.hom ≫ E'.f = E.f,
            (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of A)) (P Q : SchemeHomOver t E.f),
              mapPt e.hom he (E.L.mul t P Q) = E'.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
            (∀ x : ↥Λ, E.act x ≫ e.hom = e.hom ≫ E'.act x) ∧
            (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of A)) (P : SchemeHomOver t E.f),
              FactorsThrough E.lev P ↔ FactorsThrough E'.lev (mapPt e.hom he P))) ∧

      (∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
          (resA : A →+* ResidueField O) (hs : Function.Surjective resA) (hc : resA.comp (algebraMap O A) = residue O)
          (E E' : FakeEllipticCurve Λ 1 A) (g : u₀.1.A ⟶ E.A) (g' : u₀.1.A ⟶ E'.A)
          (hg : FakeEllipticCurve.IsPullbackVia resA E u₀.1 g) (hg' : FakeEllipticCurve.IsPullbackVia resA E' u₀.1 g')
          (e : E.A ≅ E'.A), g ≫ e.hom = g' → ∀ (he : e.hom ≫ E'.f = E.f),
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of A)) (P Q : SchemeHomOver t E.f),
              mapPt e.hom he (E.L.mul t P Q) = E'.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) →
          (∀ x : ↥Λ, E.act x ≫ e.hom = e.hom ≫ E'.act x) →
        Φ A resA hs hc E g hg = Φ A resA hs hc E' g' hg') ∧

      (∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
          (resA : A →+* ResidueField O) (hs : Function.Surjective resA) (hc : resA.comp (algebraMap O A) = residue O)
          (χ : R →ₐ[O] A), resA.comp χ.toRingHom = resR →
        ∃ (E : FakeEllipticCurve Λ 1 A) (g : u₀.1.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia resA E u₀.1 g),
          Φ A resA hs hc E g hg = χ) ∧

      (∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
          (resA : A →+* ResidueField O) (hs : Function.Surjective resA) (hc : resA.comp (algebraMap O A) = residue O)
          (A' : Type) [CommRing A'] [IsLocalRing A'] [IsArtinianRing A'] [Algebra O A']
          (resA' : A' →+* ResidueField O) (hs' : Function.Surjective resA') (hc' : resA'.comp (algebraMap O A') = residue O)
          (f : A →ₐ[O] A'), resA'.comp f.toRingHom = resA →
        ∀ (E : FakeEllipticCurve Λ 1 A) (E' : FakeEllipticCurve Λ 1 A') (k : E'.A ⟶ E.A),
          FakeEllipticCurve.IsPullbackVia f.toRingHom E E' k →
        ∀ (g' : u₀.1.A ⟶ E'.A) (hg' : FakeEllipticCurve.IsPullbackVia resA' E' u₀.1 g')
          (hg : FakeEllipticCurve.IsPullbackVia resA E u₀.1 (g' ≫ k)),
          Φ A' resA' hs' hc' E' g' hg' = f.comp (Φ A resA hs hc E (g' ≫ k) hg)) := by sorry
