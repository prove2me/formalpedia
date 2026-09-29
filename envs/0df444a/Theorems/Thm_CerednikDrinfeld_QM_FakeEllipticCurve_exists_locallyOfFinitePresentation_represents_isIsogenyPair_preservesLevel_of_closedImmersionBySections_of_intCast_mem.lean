-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_locallyOfFinitePresentation_represents_isIsogenyPair_preservesLevel_of_closedImmersionBySections_of_intCast_mem
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_locallyOfFinitePresentation_represents_isIsogenyPair_preservesLevel_of_closedImmersionBySections_of_intCast_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/bf171bb8-d366-5e89-b2d8-48af2134333e
-- title:
--   Representability of level-preserving degree rᵈ isogeny pairs
-- statement:
--   Fix $a,b\in\mathbb{Q}$, a $\mathbb{Z}$-submodule $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ containing the image of every integer, a level $N$, a family $\beta:\mathrm{Fin}\,4\to\Lambda$ such that each element of $\Lambda$ is a unique integral combination of the $\beta_j$ (so $\beta$ is a $\mathbb{Z}$-basis of rank $4$), a prime $r$ and $d\in\mathbb{N}$. Let $S$ be a commutative ring and $E,A$ fake elliptic curves of level $N$ with $\Lambda$-action over $S$, each carrying a module $\mathcal{L}_E$ on $E.A$, resp. $\mathcal{L}_A$ on $A.A$, that is invertible (every point has a neighbourhood on which the restriction is isomorphic to the unit module) and admits a projective presentation by global sections whose associated morphism to $\mathbb{P}^{N'}_S$ is a closed immersion. Then there are a scheme $X$, a morphism $\xi:X\to\operatorname{Spec}S$ locally of finite presentation, and a rule $\mathrm{pt}$ assigning to every $S$-algebra $T$, every pair $E',A'$ of fake elliptic curves over $T$ together with morphisms $g_E:E'.A\to E.A$, $g_A:A'.A\to A.A$ exhibiting them as pullbacks of $E,A$ along $\operatorname{Spec}T\to\operatorname{Spec}S$ in the sense of `IsPullbackVia` (cartesian square, compatibility with the relative group laws and the $\Lambda$-actions, and points factoring through the level structure of $E'$ mapping to points factoring through that of $E$), and every pair $\varphi:E'.A\to A'.A$, $\varphi':A'.A\to E'.A$ with $\varphi$ a morphism over $T$ forming an isogeny pair of degree $r^{d}$ (each compatible with the group laws, $\Lambda$-equivariant, and $\varphi\varphi'=[r^{d}]$, $\varphi'\varphi=[r^{d}]$ whenever $r^{d}\in\Lambda$) with $\varphi$ preserving level, a $T$-point of $\xi$ over $\operatorname{Spec}S$, such that: the point is unchanged under isomorphisms $i_E,i_A$ of the two presentations satisfying `IsoVia`, compatible with the comparison morphisms and intertwining the forward maps; $\mathrm{pt}$ commutes with base change along any $S$-algebra map $T\to T'$ (for pullbacks of the data intertwining both maps of the pair); every $T$-point of $\xi$ over $\operatorname{Spec}S$ is of the form $\mathrm{pt}(\varphi,\varphi')$ for some such pair; and $\mathrm{pt}$ determines the pair, i.e. equal points force $\varphi_1=\varphi_2$ and $\varphi_1'=\varphi_2'$.
--
--   This is the representability statement for the functor of level-preserving $\Lambda$-equivariant isogeny pairs of degree $r^{d}$ between two fixed fake elliptic curves, in the shape of a scheme locally of finite presentation over the base together with a natural bijection on points; the separatedness recorded in the underlying representability result is not carried in this conclusion, while the level-preservation condition and the injectivity of the point rule on pairs (which uses that $r^{d}\neq 0$ and that $\Lambda$ contains the integers) are. It feeds the construction of fine moduli of fake elliptic curves with isogeny and full level structure used in the Čerednik–Drinfeld part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_locallyOfFinitePresentation_represents_isIsogenyPair_preservesLevel_of_closedImmersionBySections_of_intCast_mem.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_locallyOfFinitePresentation_represents_isIsogenyPair_preservesLevel_of_closedImmersionBySections_of_intCast_mem
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j) (r d : ℕ) [Fact r.Prime]
    (S : Type) [CommRing S] (E A : FakeEllipticCurve Λ N S)
    (𝓛E : E.A.Modules) (hE₁ : Scheme.Modules.IsInvertible 𝓛E) (hE₂ : Scheme.Modules.ClosedImmersionBySections 𝓛E E.f)
    (𝓛A : A.A.Modules) (hA₁ : Scheme.Modules.IsInvertible 𝓛A) (hA₂ : Scheme.Modules.ClosedImmersionBySections 𝓛A A.f) :
    ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
      (pt : ∀ (T : Type) [CommRing T] [Algebra S T]
        (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
        (gA : A'.A ⟶ A.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
        (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f),
        FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ' → FakeEllipticCurve.PreservesLevel E' A' φ hφ →
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S T))) ξ),

      (∀ (T : Type) [CommRing T] [Algebra S T]
          (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
          (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
          (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
          (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ') (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ)
          (E'' A'' : FakeEllipticCurve Λ N T) (gE'' : E''.A ⟶ E.A) (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E'' gE'')
          (gA'' : A''.A ⟶ A.A) (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A'' gA'')
          (ψ : E''.A ⟶ A''.A) (ψ' : A''.A ⟶ E''.A) (hψ : ψ ≫ A''.f = E''.f)
          (hq : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' ψ ψ') (hm : FakeEllipticCurve.PreservesLevel E'' A'' ψ hψ)
          (iE : E'.A ≅ E''.A) (hiE : iE.hom ≫ E''.f = E'.f) (iA : A'.A ≅ A''.A) (hiA : iA.hom ≫ A''.f = A'.f),
          FakeEllipticCurve.IsoVia E' E'' iE hiE → FakeEllipticCurve.IsoVia A' A'' iA hiA →
          iE.hom ≫ gE'' = gE → iA.hom ≫ gA'' = gA → iE.hom ≫ ψ = φ ≫ iA.hom →
            pt T E' A' gE hgE gA hgA φ φ' hφ hp hl = pt T E'' A'' gE'' hgE'' gA'' hgA'' ψ ψ' hψ hq hm) ∧

      (∀ (T T' : Type) [CommRing T] [Algebra S T] [CommRing T'] [Algebra S T'] (f : T →ₐ[S] T')
          (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
          (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
          (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
          (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ') (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ)
          (E'' A'' : FakeEllipticCurve Λ N T') (hE : E''.A ⟶ E'.A) (hhE : FakeEllipticCurve.IsPullbackVia (f : T →+* T') E' E'' hE)
          (hA : A''.A ⟶ A'.A) (hhA : FakeEllipticCurve.IsPullbackVia (f : T →+* T') A' A'' hA)
          (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T') E E'' (hE ≫ gE))
          (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T') A A'' (hA ≫ gA))
          (ψ : E''.A ⟶ A''.A) (ψ' : A''.A ⟶ E''.A) (hψ : ψ ≫ A''.f = E''.f)
          (hq : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' ψ ψ') (hm : FakeEllipticCurve.PreservesLevel E'' A'' ψ hψ),
          ψ ≫ hA = hE ≫ φ → ψ' ≫ hE = hA ≫ φ' →
            (pt T' E'' A'' (hE ≫ gE) hgE'' (hA ≫ gA) hgA'' ψ ψ' hψ hq hm).1 =
              Spec.map (CommRingCat.ofHom (f : T →+* T')) ≫ (pt T E' A' gE hgE gA hgA φ φ' hφ hp hl).1) ∧

      (∀ (T : Type) [CommRing T] [Algebra S T]
          (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
          (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
          (z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S T))) ξ),
          ∃ (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
            (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ') (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ),
            pt T E' A' gE hgE gA hgA φ φ' hφ hp hl = z) ∧

      (∀ (T : Type) [CommRing T] [Algebra S T]
          (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
          (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
          (φ₁ : E'.A ⟶ A'.A) (φ₁' : A'.A ⟶ E'.A) (hφ₁ : φ₁ ≫ A'.f = E'.f)
          (hp₁ : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ₁ φ₁') (hl₁ : FakeEllipticCurve.PreservesLevel E' A' φ₁ hφ₁)
          (φ₂ : E'.A ⟶ A'.A) (φ₂' : A'.A ⟶ E'.A) (hφ₂ : φ₂ ≫ A'.f = E'.f)
          (hp₂ : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ₂ φ₂') (hl₂ : FakeEllipticCurve.PreservesLevel E' A' φ₂ hφ₂),
          pt T E' A' gE hgE gA hgA φ₁ φ₁' hφ₁ hp₁ hl₁ = pt T E' A' gE hgE gA hgA φ₂ φ₂' hφ₂ hp₂ hl₂ → φ₁ = φ₂ ∧ φ₁' = φ₂') := by sorry
