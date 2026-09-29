-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_locallyOfFinitePresentation_isSeparated_represents_isIsogenyPair_of_closedImmersionBySections
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_locallyOfFinitePresentation_isSeparated_represents_isIsogenyPair_of_closedImmersionBySections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/3d75d0c7-a73b-5acd-9e9c-6d15fce34c27
-- title:
--   Representability of degree rᵈ isogeny pairs of fake elliptic curves
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, and a family $\beta : \mathrm{Fin}(2\cdot 2)\to\Lambda$ such that every $x\in\Lambda$ is uniquely of the form $\sum_j c_j\beta_j$ with $c_j\in\mathbb{Z}$ (so $\beta$ is a $\mathbb{Z}$-basis of $\Lambda$ of rank $4$); fix natural numbers $r,d$ and a commutative ring $S$. Let $E,A$ be fake elliptic curves over $S$ in the sense of `FakeEllipticCurve Λ N S` (a scheme with a structure morphism to $\operatorname{Spec} S$, a commutative relative group law, an abelian-scheme property bundle, all fibres of topological Krull dimension $2$, an action of $\Lambda$ by endomorphisms over the base which are additive in both senses, multiplicative in $\Lambda$ and satisfy a trace condition, together with level data). Assume each of $E$, $A$ carries a module $\mathcal{L}_E$, $\mathcal{L}_A$ that is invertible (each point has a neighbourhood on which the restriction is isomorphic to the unit module) and admits a `ProjPresentation` relative to the structure morphism, i.e. finitely many global sections giving a morphism to a projective space $\operatorname{Proj}$ of a polynomial ring over $S$ which is a closed immersion and which is compatible with the structure morphism. The conclusion asserts the existence of a scheme $Z$ with a morphism $\zeta : Z\to\operatorname{Spec} S$ that is locally of finite presentation and separated, together with a point rule $\mathrm{pt}_Z$ which assigns, to each $S$-algebra $T$, each pair of fake elliptic curves $E',A'$ over $T$ with morphisms $g_E : E'\to E$, $g_A : A'\to A$ exhibiting $E',A'$ as pullbacks of $E,A$ along $S\to T$ in the sense of `FakeEllipticCurve.IsPullbackVia` (a pullback square whose comparison map respects the group law, the $\Lambda$-action, and carries level points to level points), and each pair $\varphi : E'\to A'$ over $T$ and $\varphi' : A'\to E'$ forming an isogeny pair of degree $r^d$ in the sense of `FakeEllipticCurve.IsIsogenyPair` (both are homomorphisms for the relative group laws, both commute with the $\Lambda$-action, and whenever the integer $r^d$ lies in $\Lambda$ the composites $\varphi\varphi'$ and $\varphi'\varphi$ are the actions of $r^d$), a $T$-point of $Z$ over $\operatorname{Spec} S$, subject to four conditions: the point is unchanged when the data are transported along isomorphisms $i_E,i_A$ over $T$ satisfying `FakeEllipticCurve.IsoVia`, compatible with $g_E,g_A$ and intertwining the two legs of the pairs; for an $S$-algebra map $f : T\to T'$ and data over $T'$ pulled back from data over $T$ along $f$ with $\psi,\psi'$ compatible with $\varphi,\varphi'$, the underlying morphism of the $T'$-point is $\operatorname{Spec} f$ followed by that of the $T$-point; for fixed pullback data over $T$, every $T$-point of $Z$ over $\operatorname{Spec} S$ arises from some isogeny pair of degree $r^d$; and two isogeny pairs over $T$ with the same point have equal first legs and equal second legs.
--
--   This is the representability statement for the functor of degree $r^d$ isogeny pairs between two fake elliptic curves over a base, in the form of a separated, locally finitely presented scheme over $\operatorname{Spec} S$ together with a point rule that is natural in the base ring and bijective onto points for each choice of pullback presentation; no condition on level structures is imposed. It is obtained from the corresponding representability statement for pairs of homomorphisms intertwining the $\Lambda$-action, and is in turn used for the variant in which the isogeny pairs are required to preserve the level-$N$ data, the level condition cutting out a closed, finitely presented subscheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_locallyOfFinitePresentation_isSeparated_represents_isIsogenyPair_of_closedImmersionBySections.lean

import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_locallyOfFinitePresentation_isSeparated_represents_isIsogenyPair_of_closedImmersionBySections
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j) (r d : ℕ)
    (S : Type) [CommRing S] (E A : FakeEllipticCurve Λ N S)
    (𝓛E : E.A.Modules) (hE₁ : Scheme.Modules.IsInvertible 𝓛E) (hE₂ : Scheme.Modules.ClosedImmersionBySections 𝓛E E.f)
    (𝓛A : A.A.Modules) (hA₁ : Scheme.Modules.IsInvertible 𝓛A) (hA₂ : Scheme.Modules.ClosedImmersionBySections 𝓛A A.f) :
    ∃ (Z : Scheme.{0}) (ζ : Z ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ζ) (_ : IsSeparated ζ)
      (ptZ : ∀ (T : Type) [CommRing T] [Algebra S T]
        (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
        (gA : A'.A ⟶ A.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
        (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f),
        FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ' →
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S T))) ζ),

      (∀ (T : Type) [CommRing T] [Algebra S T]
          (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
          (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
          (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
          (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ')
          (E'' A'' : FakeEllipticCurve Λ N T) (gE'' : E''.A ⟶ E.A) (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E'' gE'')
          (gA'' : A''.A ⟶ A.A) (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A'' gA'')
          (ψ : E''.A ⟶ A''.A) (ψ' : A''.A ⟶ E''.A) (hψ : ψ ≫ A''.f = E''.f)
          (hq : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' ψ ψ')
          (iE : E'.A ≅ E''.A) (hiE : iE.hom ≫ E''.f = E'.f) (iA : A'.A ≅ A''.A) (hiA : iA.hom ≫ A''.f = A'.f),
          FakeEllipticCurve.IsoVia E' E'' iE hiE → FakeEllipticCurve.IsoVia A' A'' iA hiA →
          iE.hom ≫ gE'' = gE → iA.hom ≫ gA'' = gA → iE.hom ≫ ψ = φ ≫ iA.hom → iA.hom ≫ ψ' = φ' ≫ iE.hom →
            ptZ T E' A' gE hgE gA hgA φ φ' hφ hp = ptZ T E'' A'' gE'' hgE'' gA'' hgA'' ψ ψ' hψ hq) ∧

      (∀ (T T' : Type) [CommRing T] [Algebra S T] [CommRing T'] [Algebra S T'] (f : T →ₐ[S] T')
          (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
          (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
          (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
          (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ')
          (E'' A'' : FakeEllipticCurve Λ N T') (hE : E''.A ⟶ E'.A) (hhE : FakeEllipticCurve.IsPullbackVia (f : T →+* T') E' E'' hE)
          (hA : A''.A ⟶ A'.A) (hhA : FakeEllipticCurve.IsPullbackVia (f : T →+* T') A' A'' hA)
          (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T') E E'' (hE ≫ gE))
          (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T') A A'' (hA ≫ gA))
          (ψ : E''.A ⟶ A''.A) (ψ' : A''.A ⟶ E''.A) (hψ : ψ ≫ A''.f = E''.f)
          (hq : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' ψ ψ'),
          ψ ≫ hA = hE ≫ φ → ψ' ≫ hE = hA ≫ φ' →
            (ptZ T' E'' A'' (hE ≫ gE) hgE'' (hA ≫ gA) hgA'' ψ ψ' hψ hq).1 =
              Spec.map (CommRingCat.ofHom (f : T →+* T')) ≫ (ptZ T E' A' gE hgE gA hgA φ φ' hφ hp).1) ∧

      (∀ (T : Type) [CommRing T] [Algebra S T]
          (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
          (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
          (z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S T))) ζ),
          ∃ (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
            (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ'),
            ptZ T E' A' gE hgE gA hgA φ φ' hφ hp = z) ∧

      (∀ (T : Type) [CommRing T] [Algebra S T]
          (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
          (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
          (φ₁ : E'.A ⟶ A'.A) (φ₁' : A'.A ⟶ E'.A) (hφ₁ : φ₁ ≫ A'.f = E'.f)
          (hp₁ : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ₁ φ₁')
          (φ₂ : E'.A ⟶ A'.A) (φ₂' : A'.A ⟶ E'.A) (hφ₂ : φ₂ ≫ A'.f = E'.f)
          (hp₂ : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ₂ φ₂'),
          ptZ T E' A' gE hgE gA hgA φ₁ φ₁' hφ₁ hp₁ = ptZ T E' A' gE hgE gA hgA φ₂ φ₂' hφ₂ hp₂ → φ₁ = φ₂ ∧ φ₁' = φ₂') := by sorry
