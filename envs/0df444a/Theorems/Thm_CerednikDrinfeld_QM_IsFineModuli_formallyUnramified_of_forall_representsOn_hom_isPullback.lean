-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_formallyUnramified_of_forall_representsOn_hom_isPullback
-- name    : CerednikDrinfeld.QM.IsFineModuli.formallyUnramified_of_forall_representsOn_hom_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/73bae4ca-6683-52fe-8838-152f4aa92197
-- title:
--   Formal unramifiedness of the glued isogeny-pair stratum
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$, naturals $N$, $r$, $d$, $n$, a commutative ring $\mathcal{O}$, a scheme $M$ with a morphism $f_M : M \to \operatorname{Spec}\mathcal{O}$, and a point rule $\mathrm{ptF}$ which to every commutative ring $S$, every $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal{O}$ and every pair consisting of a fake elliptic curve over $S$ for $(\Lambda,N)$ together with a full level-$n$ structure assigns a morphism $\operatorname{Spec} S \to M$ composing with $f_M$ to $s$; assume `IsFineModuli`, i.e. $\mathrm{ptF}$ is invariant under isomorphism of curves-with-level, compatible with base change along ring maps, surjective onto morphisms over $s$, and injective up to isomorphism. Let $C$ be an $\mathcal{O}$-algebra, $\mathfrak{A}$ a fake elliptic curve over $C$, and assume every integer lies in $\Lambda$. Assume (`hloc`) that for every ring $S$ that is an $\mathcal{O}$- and $C$-algebra compatibly, every curve-with-level $u$ over $S$ and every $A$ exhibited by a morphism $g_A$ as the pullback of $\mathfrak{A}$ along $C \to S$ (pullback square on total spaces, compatible with group law, $\Lambda$-action and level), there are a scheme $X$ and $\xi : X \to \operatorname{Spec} S$ locally of finite presentation carrying a family $\mathrm{pt}$ with `RepresentsOn r d u.1 A ξ pt`, so that $\xi$ represents level-preserving isogeny pairs of degree $r^{d}$ between pullbacks of $u.1$ and of $A$. Let $q : X_d \to M \times_{\operatorname{Spec}\mathcal{O}} \operatorname{Spec} C$ be a morphism, and $\kappa$ a rule producing from each such datum a chart $X \to X_d$, subject to (`hB1`) $\kappa$ followed by $q$ and the first projection equals $\xi$ followed by the moduli point $\mathrm{ptF}$ of $u$, and followed by the second projection equals $\xi$ followed by $\operatorname{Spec}(C \to S)$, and (`hB2`) for every scheme $T$ with $x : T \to X_d$ and $t : T \to \operatorname{Spec} S$ satisfying these two identities there is a unique $y : T \to X$ with $y$ followed by $\kappa$ equal to $x$ and $y$ followed by $\xi$ equal to $t$. Then $q$ is formally unramified.
--
--   This is the global form of the statement that the degree-$r^{d}$ isogeny-pair stratum, glued out of local representing schemes over charts of the fine moduli scheme of fake elliptic curves with full level structure, is formally unramified over $M \times_{\operatorname{Spec}\mathcal{O}} \operatorname{Spec} C$; the cartesian charts supplied by $\kappa$, (`hB1`) and (`hB2`) reduce it to the local representability statement. It feeds the construction of the rigidified-curve strata used in the Čerednik–Drinfeld description of the relevant quaternionic moduli.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_formallyUnramified_of_forall_representsOn_hom_isPullback.lean

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

theorem CerednikDrinfeld.QM.IsFineModuli.formallyUnramified_of_forall_representsOn_hom_isPullback
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (r d : ℕ)

    (𝒪 : Type) [CommRing 𝒪] (n : ℕ) (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)

    (C : Type) [CommRing C] [Algebra 𝒪 C] (𝔄 : FakeEllipticCurve Λ N C)
    (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)

    (hloc : ∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S)
      (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
        FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)

    (Xd : Scheme.{0}) (q : Xd ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
    (κ : ∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
        (u : FakeEllipticCurve.WithFullLevel Λ N n S)
        (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA)
        (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
        FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xd))
    (hB1 : (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA)
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
          κ S u A gA hgA X ξ pt hX ≫ q ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
              ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
          κ S u A gA hgA X ξ pt hX ≫ q ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
              ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap C S))))
    (hB2 : (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA)
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (T : Scheme.{0}) (x : T ⟶ Xd) (t : T ⟶ Spec (CommRingCat.of S)),
          x ≫ q ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) = t ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 →
          x ≫ q ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) = t ≫ Spec.map (CommRingCat.ofHom (algebraMap C S)) →
            ∃! y : T ⟶ X, y ≫ κ S u A gA hgA X ξ pt hX = x ∧ y ≫ ξ = t)) :
    FormallyUnramified q := by sorry
