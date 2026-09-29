-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_iso_comp_eq_of_isClosedImmersion_of_forall_app_awayToSection_eq_zero_iff
-- name    : AlgebraicGeometry.ProjSpace.exists_iso_comp_eq_of_isClosedImmersion_of_forall_app_awayToSection_eq_zero_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/a75cfb96-e369-52d2-88f5-bac505e7ff60
-- title:
--   Closed subschemes of Pⁿ_A determined by chartwise vanishing in high degrees
-- statement:
--   Let $A$ be a commutative ring, let $n, m$ be natural numbers, and let $Z, Z'$ be schemes equipped with closed immersions $\iota : Z \to \operatorname{Proj} A[x_0,\dots,x_n]$ and $\iota' : Z' \to \operatorname{Proj} A[x_0,\dots,x_n]$, the $\operatorname{Proj}$ being taken for the standard grading of `MvPolynomial (Fin (n+1)) A` by `MvPolynomial.homogeneousSubmodule`. For an index $i$ and a form $F$ homogeneous of degree $d$, write $F/x_i^d$ for the element of the degree-zero homogeneous localisation away from $x_i$ given by numerator $F$ and denominator $x_i^d$, and let $\iota^\ast(F/x_i^d)$ denote the image, under the map on sections induced by $\iota$ over the basic open set $D_+(x_i)$, of the section of the structure sheaf of $\operatorname{Proj}$ attached to $F/x_i^d$ by `Proj.awayToSection`. The hypothesis is that for every $d \ge m$ and every $F$ homogeneous of degree $d$, one has $\iota^\ast(F/x_i^d) = 0$ for all $i \in \{0,\dots,n\}$ if and only if $\iota'^\ast(F/x_i^d) = 0$ for all $i$. The conclusion is that there exists an isomorphism of schemes $e : Z \cong Z'$ with $\iota' \circ e = \iota$, so that the two closed immersions have the same image as closed subschemes.
--
--   This is the statement that a closed subscheme of projective space over a ring is determined by the degrees $\ge m$ part of its saturated homogeneous ideal, read off chart by chart on the standard affine charts $D_+(x_i)$. It is used in the construction of projective embeddings of framed polarised abelian schemes over a Noetherian base, where a subscheme is pinned down by the forms vanishing on it in all sufficiently large degrees.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_exists_iso_comp_eq_of_isClosedImmersion_of_forall_app_awayToSection_eq_zero_iff.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_iso_comp_eq_of_isClosedImmersion_of_forall_app_awayToSection_eq_zero_iff
    {A : Type} [CommRing A] (n m : ℕ)
    {Z Z' : Scheme.{0}} (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A))
    (ι' : Z' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A))
    [IsClosedImmersion ι] [IsClosedImmersion ι']
    (h : ∀ (d : ℕ), m ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d),
      ((∀ i : Fin (n + 1),
          ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
            ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
              (HomogeneousLocalization.mk
                { deg := d
                  num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                  den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                  den_mem := ⟨d, rfl⟩ })) = 0) ↔
       (∀ i : Fin (n + 1),
          ι'.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
            ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
              (HomogeneousLocalization.mk
                { deg := d
                  num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                  den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                  den_mem := ⟨d, rfl⟩ })) = 0))) :
    ∃ e : Z ≅ Z', e.hom ≫ ι' = ι := by sorry
