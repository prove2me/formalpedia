-- Prove2me | Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_isPullback_projMap_of_isBaseChange
-- name    : AlgebraicGeometry.GradedOAlgebra.isPullback_projMap_of_isBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/541378f9-c334-528d-ab38-becbd21995ed
-- title:
--   Proj of a degreewise base change is cartesian
-- statement:
--   Let $S$ be a commutative ring, $S'$ a commutative $S$-algebra, $R$ a commutative $S$-algebra equipped with a family $\mathcal{R} : \mathbb{N} \to$ Submodule $S\,R$ making it an $\mathbb{N}$-graded $S$-algebra, and $R'$ a commutative $S'$-algebra which is also an $S$-algebra compatibly (scalar tower $S \to S' \to R'$), equipped with a grading $\mathcal{R}'$ by $S'$-submodules. Let $\vartheta : R \to R'$ be an $S$-algebra homomorphism with $\vartheta(\mathcal{R}_n) \subseteq \mathcal{R}'_n$ for all $n$, and assume that for every $n$ the induced $S$-linear map $\mathcal{R}_n \to \mathcal{R}'_n$ (the latter viewed as an $S$-module by restriction of scalars) exhibits $\mathcal{R}'_n$ as the base change of $\mathcal{R}_n$ along $S \to S'$, i.e. $\mathcal{R}'_n \cong S' \otimes_S \mathcal{R}_n$. Assume further that the irrelevant homogeneous ideal of $\mathcal{R}'$ is contained in the image under the graded ring homomorphism induced by $\vartheta$ of the irrelevant homogeneous ideal of $\mathcal{R}$, so that a morphism $\operatorname{Proj} \mathcal{R}' \to \operatorname{Proj}\mathcal{R}$ is defined. Then the square formed by this morphism $\operatorname{Proj}\mathcal{R}' \to \operatorname{Proj}\mathcal{R}$, the structure morphisms $\operatorname{Proj}\mathcal{R}' \to \operatorname{Spec} S'$ and $\operatorname{Proj}\mathcal{R} \to \operatorname{Spec} S$ (each given by `Proj.toSpecZero` followed by $\operatorname{Spec}$ of the degree-zero projection composed with the respective structure map $S' \to R'$, resp. $S \to R$), and $\operatorname{Spec} S' \to \operatorname{Spec} S$, is a pullback square; that is, $\operatorname{Proj}\mathcal{R}' \cong \operatorname{Proj}\mathcal{R} \times_{\operatorname{Spec} S} \operatorname{Spec} S'$.
--
--   This is the compatibility of the Proj construction with base change of the graded algebra along $S \to S'$ (EGA II 2.8.10, 3.5.3), in the form asserting that the induced morphism of Proj schemes is cartesian rather than merely that some isomorphism exists. It feeds into the descent statement [`AlgebraicGeometry.exists_descent_of_faithfullyFlat_of_cocycle`](thm.html#AlgebraicGeometry.exists_descent_of_faithfullyFlat_of_cocycle), where projective schemes obtained by base change must be recognised as pullbacks.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_GradedOAlgebra_isPullback_projMap_of_isBaseChange.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomogeneousLocalization

theorem AlgebraicGeometry.GradedOAlgebra.isPullback_projMap_of_isBaseChange
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (R' : Type u) [CommRing R'] [Algebra S' R'] [Algebra S R'] [IsScalarTower S S' R']
    (𝓡' : ℕ → Submodule S' R') [GradedAlgebra 𝓡']
    (ϑ : R →ₐ[S] R') (hϑdeg : ∀ n, ∀ x ∈ 𝓡 n, ϑ x ∈ 𝓡' n)
    (hbc : ∀ n, IsBaseChange S' ((ϑ.toLinearMap.restrict (p := 𝓡 n) (q := (𝓡' n).restrictScalars S) (hϑdeg n))
      : 𝓡 n →ₗ[S] (𝓡' n).restrictScalars S))
    (hirr : HomogeneousIdeal.irrelevant 𝓡' ≤
      (HomogeneousIdeal.irrelevant 𝓡).map ({ ϑ.toRingHom with map_mem := fun h => hϑdeg _ _ h } : 𝓡 →+*ᵍ 𝓡')) :
    IsPullback (Proj.map ({ ϑ.toRingHom with map_mem := fun h => hϑdeg _ _ h } : 𝓡 →+*ᵍ 𝓡') hirr)
      (Proj.toSpecZero 𝓡' ≫ Spec.map (CommRingCat.ofHom ((GradedRing.projZeroRingHom' 𝓡').comp (algebraMap S' R'))))
      (Proj.toSpecZero 𝓡 ≫ Spec.map (CommRingCat.ofHom ((GradedRing.projZeroRingHom' 𝓡).comp (algebraMap S R))))
      (Spec.map (CommRingCat.ofHom (algebraMap S S'))) := by sorry
