-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
-- name    : AlgebraicGeometry.ProjSpace.isPullback_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/b0c3d8f6-bffa-515d-a45a-3c3271585c3d
-- title:
--   Projective space is stable under base change
-- statement:
--   Let $R$ and $A$ be commutative rings in a common universe, with $A$ an $R$-algebra, and let $n$ be a natural number. Write $\mathcal{A}_R$ for the graded ring $\bigoplus_d$ of homogeneous components of the polynomial ring $R[x_0,\dots,x_n]$ in $\mathrm{Fin}(n+1)$ variables (the `MvPolynomial.homogeneousSubmodule` grading), and similarly $\mathcal{A}_A$ over $A$, so that $\operatorname{Proj}\mathcal{A}_R$ and $\operatorname{Proj}\mathcal{A}_A$ are the projective spaces $\mathbb{P}^n_R$, $\mathbb{P}^n_A$. The morphism `ProjSpace.map R A n` is $\operatorname{Proj}$ applied to the graded ring homomorphism $\mathcal{A}_R \to \mathcal{A}_A$ given by coefficientwise application of `algebraMap R A`, which preserves degrees, together with the inclusion of the irrelevant ideal into its preimage; it goes from $\operatorname{Proj}\mathcal{A}_A$ to $\operatorname{Proj}\mathcal{A}_R$. Let `ProjSpace.π R n` and `ProjSpace.π A n` be the structure morphisms of these projective spaces to $\operatorname{Spec} R$ and $\operatorname{Spec} A$. The assertion is that the square with top edge `ProjSpace.map R A n`, left edge `ProjSpace.π A n`, right edge `ProjSpace.π R n` and bottom edge $\operatorname{Spec}$ of $\operatorname{algebraMap} R A$ is a pullback square of schemes: it commutes, and the resulting morphism $\mathbb{P}^n_A \to \mathbb{P}^n_R \times_{\operatorname{Spec} R} \operatorname{Spec} A$ is an isomorphism.
--
--   This is the standard statement that projective space commutes with base change, $\mathbb{P}^n_A \cong \mathbb{P}^n_R \times_{\operatorname{Spec} R}\operatorname{Spec} A$ (EGA II 2.8.10). It is used throughout the construction of the moduli spaces of framed polarised abelian schemes, in particular in the arguments producing quasi-projective fine moduli spaces and in identifying base changes of projective embeddings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_isPullback_map.lean

import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

theorem AlgebraicGeometry.ProjSpace.isPullback_map (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ) :
    IsPullback (ProjSpace.map R A n) (ProjSpace.π A n) (ProjSpace.π R n)
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by sorry
