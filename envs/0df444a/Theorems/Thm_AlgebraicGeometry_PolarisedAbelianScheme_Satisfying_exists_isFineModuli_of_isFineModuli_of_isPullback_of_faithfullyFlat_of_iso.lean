-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_exists_isFineModuli_of_isFineModuli_of_isPullback_of_faithfullyFlat_of_iso
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_isFineModuli_of_isFineModuli_of_isPullback_of_faithfullyFlat_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/a9339352-190e-5012-8e76-e35b74411fe5
-- title:
--   Descent of fine moduli along a faithfully flat base extension
-- statement:
--   Fix natural numbers $g,d,n$ and a property $Q$ assigning to every commutative ring $S$ and every `PolarisedAbelianScheme g d n S` (a scheme $A\to\operatorname{Spec} S$ with a commutative relative group law, all fibres of dimension $g$, a family $P_i$, $i<2g$, of $n$-torsion sections which on each geometrically algebraically closed fibre freely generates the $n$-torsion, together with an invertible module `pol` that is very ample with geometric fibre $H^0$-rank $d$) a proposition. Assume $Q$ is stable under base change along ring maps (in the sense of `PolarisedAbelianScheme.IsPullback`, i.e. a cartesian square of total spaces compatible with group law, the points $P_i$ and the polarisation), stable under `PolarisedAbelianScheme.Iso` (an isomorphism over $S$ respecting the group law and the $P_i$, with the polarisations matching locally on the base), that $3\le n$, and that $Q$ descends along $S\to S\otimes_{\mathcal O}\mathcal O'$, where $\mathcal O$ is a commutative ring in which $n$ is a unit and $\mathcal O'$ is an $\mathcal O$-algebra faithfully flat as an $\mathcal O$-module. Let $\pi_{M'}:M'\to\operatorname{Spec}\mathcal O'$ together with a point assignment $\mathrm{pt}'$ be a fine moduli scheme for the objects satisfying $Q$: $\mathrm{pt}'$ is constant on isomorphism classes, compatible with pullbacks, surjective onto the $S$-points over each $s:\operatorname{Spec} S\to\operatorname{Spec}\mathcal O'$, and injective up to isomorphism. Let $\pi_M:M\to\operatorname{Spec}\mathcal O$ and $q:M'\to M$ make the square with $\pi_{M'}$, $\pi_M$ and $\operatorname{Spec}(\mathcal O\to\mathcal O')$ cartesian, and assume that for every $S$, any two $s_1,s_2:\operatorname{Spec} S\to\operatorname{Spec}\mathcal O'$ with equal composites to $\operatorname{Spec}\mathcal O$ and every object $X$ over $S$ satisfying $Q$, the points $\mathrm{pt}'(s_1,X)$ and $\mathrm{pt}'(s_2,X)$ have the same image under $q$. Then there exists a point assignment $\mathrm{pt}$ over $\operatorname{Spec}\mathcal O$ making $\pi_M$ a fine moduli scheme for the objects satisfying $Q$, in the same four-part sense.
--
--   This is the fpqc descent step for representability: a fine moduli scheme over $\mathcal O'$ whose structure morphism is the base change of a given $\mathcal O$-scheme $M$ descends to make $M$ a fine moduli scheme over $\mathcal O$. It is used by [`AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_isFineModuli_of_forall_exists_isFineModuli_of_primitiveRoot`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_isFineModuli_of_forall_exists_isFineModuli_of_primitiveRoot), where the auxiliary base $\mathcal O'$ is obtained by adjoining a primitive $n$-th root of unity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_exists_isFineModuli_of_isFineModuli_of_isPullback_of_faithfullyFlat_of_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open AlgebraicGeometry
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_isFineModuli_of_isFineModuli_of_isPullback_of_faithfullyFlat_of_iso
    (g d n : ℕ) (Q : ∀ (S : Type) [CommRing S], PolarisedAbelianScheme g d n S → Prop)
    (hQbc : ∀ {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
      (u : PolarisedAbelianScheme g d n S) (u' : PolarisedAbelianScheme g d n S'),
      PolarisedAbelianScheme.IsPullback φ u u' → Q S u → Q S' u')
    (hQiso : ∀ {S : Type} [CommRing S] (u u' : PolarisedAbelianScheme g d n S),
      PolarisedAbelianScheme.Iso u u' → Q S u → Q S u')
    (hn : 3 ≤ n) (𝒪 : Type) [CommRing 𝒪] (hn' : IsUnit ((n : ℕ) : 𝒪))
    (𝒪' : Type) [CommRing 𝒪'] [Algebra 𝒪 𝒪'] [Module.FaithfullyFlat 𝒪 𝒪']
    (hQdesc : ∀ (S : Type) [CommRing S] [Algebra 𝒪 S]
      (u : PolarisedAbelianScheme g d n S) (u' : PolarisedAbelianScheme g d n (S ⊗[𝒪] 𝒪')),
      PolarisedAbelianScheme.IsPullback (algebraMap S (S ⊗[𝒪] 𝒪')) u u' → Q (S ⊗[𝒪] 𝒪') u' → Q S u)

    (M' : Scheme.{0}) (πM' : M' ⟶ Spec (CommRingCat.of 𝒪'))
    (pt' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪')),
      PolarisedAbelianScheme.Satisfying g d n Q S → SchemeHomOver s πM')
    (hM' : PolarisedAbelianScheme.Satisfying.IsFineModuli g d n Q M' πM' pt')

    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of 𝒪)) (q : M' ⟶ M)
    (hq : CategoryTheory.IsPullback q πM' πM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 𝒪'))))

    (hind : ∀ (S : Type) [CommRing S] (s₁ s₂ : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪'))
      (_ : s₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 𝒪')) = s₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 𝒪')))
      (X : PolarisedAbelianScheme.Satisfying g d n Q S), (pt' S s₁ X).1 ≫ q = (pt' S s₂ X).1 ≫ q) :
    ∃ pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
        PolarisedAbelianScheme.Satisfying g d n Q S → SchemeHomOver s πM,
      PolarisedAbelianScheme.Satisfying.IsFineModuli g d n Q M πM pt := by sorry
