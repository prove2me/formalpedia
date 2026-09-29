-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_exists_locallyOfFinitePresentation_forall_representsOn_hom_isPullback_of_forall_withFullLevel
-- name    : CerednikDrinfeld.QM.IsFineModuli.exists_locallyOfFinitePresentation_forall_representsOn_hom_isPullback_of_forall_withFullLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/b06f96c6-c4e4-51ed-b3d2-0495a090471e
-- title:
--   Gluing isogeny-pair representing schemes over a fine moduli scheme
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of $\mathbb{H}[\mathbb{Q},a,b]$, naturals $N$, $r$, $d$, $n$, a commutative ring $\mathcal{O}$, a scheme $M$ with a morphism $f_M : M \to \operatorname{Spec}\mathcal{O}$, and a rule $\mathrm{ptF}$ attaching to each commutative ring $S$, each $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal{O}$ and each pair $u = (E,P)$ consisting of a fake elliptic curve over $S$ with level $N$ and a full level-$n$ structure a morphism $\operatorname{Spec} S \to M$ composing with $f_M$ to $s$; assume `IsFineModuli`, i.e. $\mathrm{ptF}$ is constant on isomorphism classes, compatible with base change along ring maps, and a bijection onto the sections of $f_M$ over $s$ up to isomorphism. Fix an $\mathcal{O}$-algebra $C$ and a fake elliptic curve $\mathfrak{A}$ over $C$. Assume rigidity: over every $C$-algebra $S$, an automorphism $e$ of $u.1.A$ over $S$ that is compatible with the relative group law and with the $\Lambda$-action and fixes the full-level point $u.2.P$ is the identity. Assume representability: for every $S$ that is a $C$- and $\mathcal{O}$-algebra compatibly, every $u$ over $S$, and every $A$ with $g_A : A.A \to \mathfrak{A}.A$ exhibiting $A$ as the pullback of $\mathfrak{A}$ along $C \to S$ (as a curve with group law, $\Lambda$-action and level), the level-preserving isogeny pairs of degree $r^d$ between pullbacks of $u.1$ and of $A$ are represented by some $\xi : X \to \operatorname{Spec} S$ locally of finite presentation with point family $\mathrm{pt}$. The conclusion provides a scheme $X_d$, a morphism $q : X_d \to M \times_{\operatorname{Spec}\mathcal{O}} \operatorname{Spec} C$ locally of finite presentation, and a rule $\kappa$ assigning to each $S$, $u$, $A$, $g_A$ and each representing datum $(X,\xi,\mathrm{pt})$ a morphism $X \to X_d$, such that: (i) $\kappa$ followed by $q$ and the first projection equals $\xi$ followed by the classifying morphism $\mathrm{ptF}\,S\,(\operatorname{Spec}(\mathcal{O} \to S))\,u$, and $\kappa$ followed by $q$ and the second projection equals $\xi$ followed by $\operatorname{Spec}(C \to S)$; (ii) this square is cartesian in the elementwise sense: for every scheme $T$ and morphisms $x : T \to X_d$, $t : T \to \operatorname{Spec} S$ agreeing after the two projections with $t$ followed by the classifying morphism respectively by $\operatorname{Spec}(C \to S)$, there is a unique $y : T \to X$ with $y$ followed by $\kappa$ equal to $x$ and $y$ followed by $\xi$ equal to $t$; (iii) $\kappa$ is compatible with base change: given a compatible tower $\mathcal{O} \to C \to S \to S'$, data $u$ over $S$ and $u'$ over $S'$ with $g : u'.1.A \to u.1.A$ realising $u'.1$ as the pullback of $u.1$ along $S \to S'$ and matching the full-level points, $A$ over $S$ pulled back from $\mathfrak{A}$, $A'$ over $S'$ pulled back from $A$ along $h_A$ and from $\mathfrak{A}$ along $h_A$ followed by $g_A$, representing data $(X,\xi,\mathrm{pt})$ and $(X',\xi',\mathrm{pt}')$, and $e : X' \to X$ making $(e,\xi',\xi,\operatorname{Spec}(S \to S'))$ a pullback square and identifying the two point families (for every $T$ over $S'$ and $S$ compatibly, all pullbacks $E''$, $A''$ and all degree-$r^d$ level-preserving isogeny pairs between them, the point of $\mathrm{pt}'$ followed by $e$ equals the corresponding point of $\mathrm{pt}$), one has $e$ followed by $\kappa$ for the data over $S$ equal to $\kappa$ for the data over $S'$.
--
--   This is the relative representability statement that transports a local solution of the degree-$r^d$ isogeny-pair moduli problem, given over each ring carrying a curve with full level-$n$ structure, to a single scheme $X_d$ locally of finite presentation over the base change $M \times_{\operatorname{Spec}\mathcal{O}} \operatorname{Spec} C$ of the fine moduli scheme, together with cartesian charts $\kappa$ and their compatibility under base change. It feeds the construction of the functor representing rigidified fake elliptic curves in the Čerednik–Drinfeld uniformisation, being used by [`CerednikDrinfeld.QM.IsFineModuli.exists_algFunctor_represents_rigidifiedCurve_strata_unramified`](thm.html#CerednikDrinfeld.QM.IsFineModuli.exists_algFunctor_represents_rigidifiedCurve_strata_unramified).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_exists_locallyOfFinitePresentation_forall_representsOn_hom_isPullback_of_forall_withFullLevel.lean

import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogenyPairRep
import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.IsFineModuli.exists_locallyOfFinitePresentation_forall_representsOn_hom_isPullback_of_forall_withFullLevel
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (r d : ℕ)

    (𝒪 : Type) [CommRing 𝒪] (n : ℕ) (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)

    (C : Type) [CommRing C] [Algebra 𝒪 C] (𝔄 : FakeEllipticCurve Λ N C)

    (hrig : ∀ (S : Type) [CommRing S] [Algebra C S] (u : FakeEllipticCurve.WithFullLevel Λ N n S)
      (e : u.1.A ≅ u.1.A) (he : e.hom ≫ u.1.f = u.1.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
        mapPt e.hom he (u.1.L.mul t P Q) = u.1.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) →
      (∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ u.1.act x) →
      mapPt e.hom he u.2.P = u.2.P → e = Iso.refl u.1.A)

    (hloc : ∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S)
      (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
        FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt) :
    ∃ (Xd : Scheme.{0}) (q : Xd ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) (_ : LocallyOfFinitePresentation q)
      (κ : ∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
        (u : FakeEllipticCurve.WithFullLevel Λ N n S)
        (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA)
        (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
        FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xd)),

      (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA)
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
          κ S u A gA hgA X ξ pt hX ≫ q ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
              ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
          κ S u A gA hgA X ξ pt hX ≫ q ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
              ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap C S))) ∧

      (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA)
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (T : Scheme.{0}) (x : T ⟶ Xd) (t : T ⟶ Spec (CommRingCat.of S)),
          x ≫ q ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) = t ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 →
          x ≫ q ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) = t ≫ Spec.map (CommRingCat.ofHom (algebraMap C S)) →
            ∃! y : T ⟶ X, y ≫ κ S u A gA hgA X ξ pt hX = x ∧ y ≫ ξ = t) ∧

      (∀ (S S' : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          [CommRing S'] [Algebra C S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S']
          [Algebra S S'] [IsScalarTower C S S'] [IsScalarTower 𝒪 S S']
          (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
          (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (algebraMap S S') u.1 u'.1 g)
          (_ : (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (algebraMap S S')) ≫ (u.2.P).1)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA)
          (A' : FakeEllipticCurve Λ N S') (hA : A'.A ⟶ A.A) (hhA : FakeEllipticCurve.IsPullbackVia (algebraMap S S') A A' hA)
          (hgA' : FakeEllipticCurve.IsPullbackVia (algebraMap C S') 𝔄 A' (hA ≫ gA))
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (X' : Scheme.{0}) (ξ' : X' ⟶ Spec (CommRingCat.of S'))
          (pt' : FakeEllipticCurve.IsogenyPair.PtFamily r d u'.1 A' ξ')
          (hX' : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u'.1 A' ξ' pt')
          (e : X' ⟶ X),
          CategoryTheory.IsPullback e ξ' ξ (Spec.map (CommRingCat.ofHom (algebraMap S S'))) →
          (∀ (T : Type) [CommRing T] [Algebra S' T] [Algebra S T] [IsScalarTower S S' T]
              (E'' A'' : FakeEllipticCurve Λ N T)
              (gE'' : E''.A ⟶ u'.1.A) (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) u'.1 E'' gE'')
              (gA'' : A''.A ⟶ A'.A) (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) A' A'' gA'')
              (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) u.1 E'' (gE'' ≫ g))
              (hgAA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A'' (gA'' ≫ hA))
              (φ : E''.A ⟶ A''.A) (φ' : A''.A ⟶ E''.A) (hφ : φ ≫ A''.f = E''.f)
              (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' φ φ') (hl : FakeEllipticCurve.PreservesLevel E'' A'' φ hφ),
              (pt' T E'' A'' gE'' hgE'' gA'' hgA'' φ φ' hφ hp hl).1 ≫ e =
                (pt T E'' A'' (gE'' ≫ g) hgE (gA'' ≫ hA) hgAA φ φ' hφ hp hl).1) →
            e ≫ κ S u A gA hgA X ξ pt hX = κ S' u' A' (hA ≫ gA) hgA' X' ξ' pt' hX') := by sorry
