-- Prove2me | Theorems.Thm_AlgebraicGeometry_isSeparated_and_quasiCompact_and_locallyOfFinitePresentation_and_forall_finset_exists_isAffineOpen_of_isPullback_of_isImmersion
-- name    : AlgebraicGeometry.isSeparated_and_quasiCompact_and_locallyOfFinitePresentation_and_forall_finset_exists_isAffineOpen_of_isPullback_of_isImmersion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/2bfdf860-0587-55c5-bc96-0b0aeb559d07
-- title:
--   Base change of a quasi-compact finite-type immersion into P^M_R
-- statement:
--   Let $R$ be a Noetherian commutative ring, $M$ a natural number, and $H$ a scheme equipped with a morphism $j : H \to \operatorname{Proj}$ of the graded ring of homogeneous components of $\mathbb{Z}$-graded polynomials in $M+1$ variables over $R$, i.e. into $\mathbb{P}^M_R$, where $j$ is assumed to be an immersion, locally of finite type and quasi-compact. Let $\mathcal{O}$ be an $R$-algebra, and let $\pi' : H' \to \operatorname{Spec}\mathcal{O}$ and $g : H' \to H$ be morphisms of schemes forming, together with the composite of $j$ with the structure morphism `ProjSpace.π R M`, that is $\mathbb{P}^M_R \to \operatorname{Spec} R$, and with the morphism $\operatorname{Spec}\mathcal{O} \to \operatorname{Spec} R$ induced by the algebra map, a pullback square (the square with $g$ and $\pi'$ as the two morphisms out of $H'$). The conclusion is a fourfold conjunction: $\pi'$ is separated, $\pi'$ is quasi-compact, $\pi'$ is locally of finite presentation, and for every finite subset $F$ of the underlying space of $H'$ there is an open subscheme $V \subseteq H'$ which is affine and contains every point of $F$.
--
--   This packages the standard geometric consequences of being a base change of a quasi-compact, finite-type immersion into projective space over a Noetherian base: separatedness, quasi-compactness and local finite presentation of the structure morphism, together with the property that finite sets of points lie in a common affine open. It is used in the construction of a quasi-projective fine moduli scheme for framed polarised abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isSeparated_and_quasiCompact_and_locallyOfFinitePresentation_and_forall_finset_exists_isAffineOpen_of_isPullback_of_isImmersion.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.isSeparated_and_quasiCompact_and_locallyOfFinitePresentation_and_forall_finset_exists_isAffineOpen_of_isPullback_of_isImmersion
    {R : Type} [CommRing R] [IsNoetherianRing R] {M : ℕ} {H : Scheme.{0}}
    (j : H ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (M + 1)) R))
    [IsImmersion j] [LocallyOfFiniteType j] [QuasiCompact j]
    (𝒪 : Type) [CommRing 𝒪] [Algebra R 𝒪]
    {H' : Scheme.{0}} (π' : H' ⟶ Spec (CommRingCat.of 𝒪)) (g : H' ⟶ H)
    (hg : IsPullback g π' (j ≫ ProjSpace.π R M) (Spec.map (CommRingCat.ofHom (algebraMap R 𝒪)))) :
    IsSeparated π' ∧ QuasiCompact π' ∧ LocallyOfFinitePresentation π' ∧
      (∀ F : Finset H', ∃ V : H'.Opens, IsAffineOpen V ∧ ∀ x ∈ F, x ∈ V) := by sorry
