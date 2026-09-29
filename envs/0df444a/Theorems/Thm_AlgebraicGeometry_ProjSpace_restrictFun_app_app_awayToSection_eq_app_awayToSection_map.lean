-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_restrictFun_app_app_awayToSection_eq_app_awayToSection_map
-- name    : AlgebraicGeometry.ProjSpace.restrictFun_app_app_awayToSection_eq_app_awayToSection_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/bd30ee26-fb58-5aeb-80ee-d070e66139d3
-- title:
--   Compatibility of dehomogenised forms with a base-change realisation
-- statement:
--   Let $A$ be a commutative ring, $n$ a natural number, and $\iota : Z \to \operatorname{Proj}$ of the graded ring $A[x_0,\dots,x_n]$ (graded by the homogeneous submodules `MvPolynomial.homogeneousSubmodule (Fin (n+1)) A`) a morphism of schemes; let $B$ be a commutative $A$-algebra and $\iota' : Z' \to \operatorname{Proj}$ of $B[x_0,\dots,x_n]$ another such morphism. Suppose $e : Z' \to Z$ satisfies $e$ followed by $\iota$ equals $\iota'$ followed by `ProjSpace.map A B n`, the morphism $\operatorname{Proj} B[x] \to \operatorname{Proj} A[x]$ obtained by applying `Proj.map` to the graded ring homomorphism given coefficientwise by $\operatorname{MvPolynomial.map}(\mathrm{algebraMap}\ A\ B)$. Let $d \in \mathbb{N}$, let $F \in A[x_0,\dots,x_n]$ be homogeneous of degree $d$, let $i \in \{0,\dots,n\}$, and assume $\iota'^{-1}D_+(x_i) \le e^{-1}\bigl(\iota^{-1}D_+(x_i)\bigr)$ as opens of $Z'$, where $D_+(x_i)$ denotes `Proj.basicOpen` at $x_i$. Consider the degree-zero homogeneous localisation $F/x_i^{d}$, with numerator $F$ and denominator $x_i^{d}$ both of degree $d$, viewed as a section over $D_+(x_i)$ via `Proj.awayToSection`. Then its pullback under $\iota$ and then under $e$, restricted along the above inclusion of opens (the presheaf restriction map of $Z'$), coincides in $\Gamma(Z', \iota'^{-1}D_+(x_i))$ with the pullback under $\iota'$ of the corresponding section $F^B/x_i^{d}$, where $F^B$ is the image of $F$ under $\operatorname{MvPolynomial.map}(\mathrm{algebraMap}\ A\ B)$.
--
--   This is the functoriality of the standard affine charts of projective space in the coefficient ring: the dehomogenisation $F/x_i^d$ of a homogeneous form is compatible with base change $A \to B$ and with any realisation $e$ of $Z'$ over $Z$ commuting with the two projective embeddings. It is used in the comparison of Proj presentations of modules under change of base ring and in the computation of Hilbert functions on geometric fibres.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_restrictFun_app_app_awayToSection_eq_app_awayToSection_map.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.restrictFun_app_app_awayToSection_eq_app_awayToSection_map
    {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A))
    (B : Type u) [CommRing B] [Algebra A B] {Z' : Scheme.{u}}
    (ι' : Z' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B))
    (e : Z' ⟶ Z) (hcomp : e ≫ ι = ι' ≫ ProjSpace.map A B n)
    (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d) (i : Fin (n + 1))
    (h : ι' ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B) (MvPolynomial.X i) ≤
      e ⁻¹ᵁ (ι ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i))) :
    ProjSpace.restrictFun h
        ((e.app (ι ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i)))
          ((ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i)))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ })))) =
      ((ι'.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B) (MvPolynomial.X i)))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B) (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨MvPolynomial.map (algebraMap A B) F, (MvPolynomial.mem_homogeneousSubmodule d (MvPolynomial.map (algebraMap A B) F)).mpr (hF.map (algebraMap A B))⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ }))) := by sorry
