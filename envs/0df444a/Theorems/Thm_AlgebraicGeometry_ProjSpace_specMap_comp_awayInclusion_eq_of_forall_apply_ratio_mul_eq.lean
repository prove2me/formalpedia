-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_specMap_comp_awayInclusion_eq_of_forall_apply_ratio_mul_eq
-- name    : AlgebraicGeometry.ProjSpace.specMap_comp_awayInclusion_eq_of_forall_apply_ratio_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/8690d33f-e5b8-5fb1-bb9f-e127aa192447
-- title:
--   Chart-independence of homogeneous coordinates of a B-point of Pⁿ_R
-- statement:
--   Let $R$ be a commutative ring, $n$ a natural number, and let $\mathbb P^n_R$ be realised as $\operatorname{Proj}$ of the graded ring $R[x_0,\dots,x_n]$ with its grading by the submodules of homogeneous polynomials of each degree. Let $B$ be a commutative $R$-algebra, let $a : \mathrm{Fin}(n+1) \to B$ be a tuple of elements of $B$, and let $i, j$ be indices such that $a_i$ and $a_j$ are units in $B$. Let $\psi_i$ and $\psi_j$ be $R$-algebra homomorphisms to $B$ from the degree-zero part of the homogeneous localisation away from $x_i$, respectively away from $x_j$, and assume that for every index $l$ one has $\psi_i(\mathrm{ratio}\,i\,l)\cdot a_i = a_l$ and $\psi_j(\mathrm{ratio}\,j\,l)\cdot a_j = a_l$, where $\mathrm{ratio}\,i\,l$ denotes the element of the homogeneous localisation away from $x_i$ given by numerator $x_l$ and denominator $x_i$, both taken in degree $1$. Then the two morphisms of schemes obtained by composing $\operatorname{Spec}$ of $\psi_i$, respectively of $\psi_j$, with the open immersion `Proj.awayι` of the standard affine chart $D_+(x_i)$, respectively $D_+(x_j)$, into $\operatorname{Proj} R[x_0,\dots,x_n]$ are equal as morphisms $\operatorname{Spec} B \to \mathbb P^n_R$.
--
--   This is the chart-compatibility statement that makes the $B$-point with homogeneous coordinates $[a_0 : \dots : a_n]$ of projective space well defined whenever a coordinate is a unit, independently of the chart on which it is written down; it is the gluing step in the construction of morphisms to projective space. It is used in the construction of morphisms from a projective presentation of a module to $\operatorname{Proj}$, and in producing the closed immersion of a representable Grassmannian functor into projective space.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_specMap_comp_awayInclusion_eq_of_forall_apply_ratio_mul_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.specMap_comp_awayInclusion_eq_of_forall_apply_ratio_mul_eq
    (R : Type u) [CommRing R] (n : ℕ) (B : Type u) [CommRing B] [Algebra R B]
    (a : Fin (n + 1) → B) (i j : Fin (n + 1)) (hi : IsUnit (a i)) (hj : IsUnit (a j))
    (ψi : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) →ₐ[R] B)
    (ψj : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) →ₐ[R] B)
    (hψi : ∀ l, ψi (ProjSpace.ratio R n i l) * a i = a l)
    (hψj : ∀ l, ψj (ProjSpace.ratio R n j l) * a j = a l) :
    Spec.map (CommRingCat.ofHom ψi.toRingHom) ≫
        Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)
          (ProjSpace.X_mem_one R n i) one_pos =
      Spec.map (CommRingCat.ofHom ψj.toRingHom) ≫
        Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j)
          (ProjSpace.X_mem_one R n j) one_pos := by sorry
