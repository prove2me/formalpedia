-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq
-- name    : AlgebraicGeometry.ProjSpace.exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/8fa9e24f-fbd8-5b5f-b2bc-a5d02c763920
-- title:
--   Degree-d forms as global sections of φ^*𝒪(d)
-- statement:
--   Let $k$ be a commutative ring, $n$ a natural number, $Z$ a scheme and $\varphi : Z \to \operatorname{Proj}$ of the graded ring $k[x_0,\dots,x_n]$ (presented as `MvPolynomial.homogeneousSubmodule (Fin (n+1)) k`) an arbitrary morphism of schemes, and let $d$ be a natural number. Write $U_i = \varphi^{-1}D_+(x_i)$ for the open `ProjSpace.pullbackChart φ i`. The assertion is that there exists a $k$-linear map $\theta$ from the $k$-module of homogeneous polynomials of degree $d$ in $x_0,\dots,x_n$ to `ProjSpace.twistObj (φ ≫ ProjSpace.π k n) φ d ⊤`, whose elements are families $(g_i)_{i}$ with $g_i \in \Gamma(Z, \top \sqcap U_i)$ satisfying the compatibility `TwistCompat`: on $(\top \sqcap U_i) \sqcap U_j$ the restriction of $g_i$ equals the $d$-th power of the restriction of the section `ProjSpace.frameUnit φ i j` of $\Gamma(Z, U_i)$ times the restriction of $g_j$, such that two clauses hold. First, for every $F$ homogeneous of degree $d$ and every index $i$, the $i$-th component of $\theta(F)$ is the restriction along $\top \sqcap U_i \le U_i$ of the image under $\varphi^\sharp$ on $D_+(x_i)$ (that is, `φ.app` at `Proj.basicOpen … (X i)`, composed with `Proj.awayToSection`) of the homogeneous localisation element of degree $d$ with numerator $F$ and denominator $x_i^{\,d}$. Second, for such $F$, $\theta(F) = 0$ if and only if that section $\varphi^\sharp(F/x_i^{\,d}) \in \Gamma(Z, U_i)$ vanishes for every $i$.
--
--   This is the standard construction sending a form of degree $d$ on $\mathbb{P}^n_k$ to a global section of the pullback $\varphi^*\mathcal O(d)$, here realised through the chartwise twist datum `ProjSpace.twistObj`, together with the identification of the kernel of $\theta$ as the forms all of whose chart expressions $F/x_i^{\,d}$ pull back to zero. It is used in the development of the Hilbert functor, where the linear map and its kernel description feed the computations of Hilbert functions of closed subschemes of projective space.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq
    {k : Type u} [CommRing k] {n : ℕ} {Z : Scheme.{u}}
    (φ : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) (d : ℕ) :
    ∃ θ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d) →ₗ[k]
        ProjSpace.twistObj (φ ≫ ProjSpace.π k n) φ d ⊤,
      (∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d) (i : Fin (n + 1)),
        (θ ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩).val i =
          ProjSpace.restrictFun (inf_le_right : ⊤ ⊓ ProjSpace.pullbackChart φ i ≤ ProjSpace.pullbackChart φ i)
            ((φ.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ })))) ∧
      (∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
        θ ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩ = 0 ↔
          ∀ i : Fin (n + 1),
            (φ.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ })) = 0) := by sorry
